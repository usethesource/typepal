module typepal::TypePal

import Set; 
import Node;
import Map;
import IO;
import List; 
import ParseTree;
import String;
import Message;

extend typepal::ScopeGraph;
extend typepal::ExtractFRModel;

bool cdebug = false;

// Global variables, used by validate and callback (define, require, etc.)

FRModel extractedFRModel;
map[loc, AType] facts = ();
set[Fact] openFacts = {};
set[Requirement] openReqs = {};
map[loc, AType] bindings = ();
map[loc, set[Requirement]] triggersRequirement = ();
map[loc, set[Fact]] triggersFact = ();

set[Requirement] requirementJobs = {};

void printState(){
    println("facts:");
        for(Key fact <- facts){
            println("\t<fact>: <facts[fact]>");
        }
   
    println("openFacts:");
       for(Fact fact <- openFacts){
            println("\t<fact>");
        }
    println("openReqs:");
        for(rq <- openReqs){
            println("\t<rq.name> at <rq.src>:");
            for(atype <- rq.dependsOn){
                println("\t  dependsOn: <atype>");
            }
        }
    //println("triggersFact:");
    //    for(l <- triggersFact){
    //        println("\t<l>: <triggersFact[l]>");
    //    }
    //println("triggersRequirement:");
    //    for(l <- triggersRequirement){
    //        println("\t<l>: <triggersRequirement[l]>");
    //    }
}

data Exception
    = UnspecifiedIsSubtype(AType atype1, AType atype2)
    | UnspecifiedGetLUB(AType atype)
    | UndefinedLUB(AType atype1, AType atype2)
    | TypeUnavailable(Key k)
    ;

// defaults for isSubtype and getLUB
bool noIsSubtype(AType atype1, AType atype2, FRModel frm) {
    throw UnspecifiedIsSubtype(atype1, atype2);
}

AType noGetLUB(AType atype, FRModel frm){
    throw UnspecifiedGetLUB(atype);
}

bool(AType atype1, AType atype2, FRModel frm) isSubtypeFun = noIsSubtype;
AType(AType atype, FRModel frm) getLUBFun = noGetLUB;

// Error handling

str intercalateAnd(list[str] strs)
    = size(strs) == 1 ? strs[0] : intercalate(", ", strs[0..-1]) + " and " + strs[-1];

void reportError(Tree t, str msg, list[Tree] found){
    throw error("<msg>, found <intercalateAnd(["`<AType2String(typeof(f))>`" | f <- found])>", t@\loc);
}

set[Message] filterMostPrecise(set[Message] messages)
    = { msg | msg <- messages, !any(msg2 <- messages, surrounds(msg, msg2) || 
                                                      (msg.msg == msg2.msg && msg.at.begin.line > msg2.at.begin.line)) };
bool surrounds (Message msg1, Message msg2){
    // TODO: return msg1.at > msg2.at should also work but does not.
    return msg1.at.offset < msg2.at.offset && msg1.at.offset + msg1.at.length >= msg2.at.offset + msg2.at.length;
}

// Find a (possibly indirect) binding
AType find(loc src){
    if(bindings[src]?){
        v = bindings[src];
        if(tvar(loc src1) := v) return find(src1);
        return v;
    }
    if(facts[src]?){
        v = facts[src];
        if(tvar(loc src1) := v) return find(src1);
        return v;
    }
    if(isTypeVariable(src)) return tvar(src);
    throw NoSuchKey(src);
}

// Substitute a type variable first using bindings, then facts; return as is when there is no binding
AType substitute(tv: tvar(loc src)){
    if(bindings[src]?) return substitute(bindings[src]);
    if(facts[src]?) return substitute(facts[src]);
    return tv;
}

AType substitute(ut: useType(Use u)){
    try {
        k = lookup(extractedFRModel, u);
        println("useType<u> ==\> <k>");
        fk = facts[k];
        return fk != ut ? instantiate(facts[k]) : ut;  
    } catch NoKey():
        return ut;
}

AType substitute(AType atype){
    if(atype has use){
        try {
            k = lookup(extractedFRModel, atype.use);
            println("<atype> ==\> <k>");
            fk = facts[k];
            return fk != atype ? instantiate(fk) : atype;  
        } catch NoKey():
            return atype;
          catch NoSuchKey(k):
            return atype;
    } else {
        return atype;
    }
}

AType normalize(AType atype){
    if(atype has use){
        println("normalize: <atype> has use");
        try {
            k = lookup(extractedFRModel, atype.use);
            println("<atype> ==\> <k>");
            fk = facts[k];
            return fk != atype ? normalize(fk) : atype;  
        } catch NoKey():
            throw TypeUnavailable(atype.use.occ);
          catch NoSuchKey(k):
            throw TypeUnavailable(atype.use.occ);
    } else {
        return atype;
    }
}

// Recursively instantiate all type variables and useTypes in a type
AType instantiate(AType atype){
  return
      visit(atype){
        case tv: tvar(loc src) => substitute(tv)
        case AType ut => substitute(ut) when ut has use
      };
}

// Unification of two types, for now, without checks on variables
tuple[bool, map[loc, AType]] unify(AType t1, AType t2, map[loc, AType] bindings){
    if(t1 == t2) return <true, bindings>;
   
    if(tvar(loc tv1) := t1){
       if(bindings[tv1]?){
          return unify(bindings[tv1], t2, bindings);
       } else {
          return <true, (tv1 : t2) + bindings>;
       }
    }
      
    if(tvar(loc tv2) := t2){
       if(bindings[tv2]?){
         return unify(bindings[tv2], t1, bindings); 
       } else {
        return <true, (tv2 : t1) + bindings>;
      }
    }
    
    if(listType(atypes1) := t1){
       if(listType(atypes2) := t2){
          if(size(atypes1) == size(atypes2)){
            for(int i <- index(atypes1)){
                <res, bindings1> = unify(atypes1[i], atypes2[i], bindings);
                if(!res) return <res, bindings>;
                bindings += bindings1;
            }
            return <true, bindings>;
          }
       }
       return <false, ()>;
    }
   
    c1 = getName(t1); c2 = getName(t2);
    a1 = arity(t1); a2 = arity(t2);
    if(c1 != c2 || a1 != a2) return <false, bindings>;
    
    if(c1 == "use"){
       return <true, bindings>;
    }
    
    kids1 = getChildren(t1); kids2 = getChildren(t2);
    for(int i <- [0 .. a1]){
        if(AType k1 := kids1[i], AType k2 := kids2[i]){
            <res, bindings1> = unify(k1, k2, bindings);
            if(!res) return <res, bindings>;
            bindings += bindings1;
        } else {
            if( kids1[i] != kids2[i] ){
                return <false, bindings>;
            }
        }
    }
    return <true, bindings>;
}

void addFact(loc l, AType atype){
    if(cdebug)println("\naddFact: <l>, <atype>, trigF: <triggersFact[l]?{}>, trigR: <triggersRequirement[l]?{}>");
  
    deps = extractTypeDependencies(atype);
    if(allDependenciesKnown(deps, facts)){
        iatype = instantiate(atype);
        if(cdebug)println("add2: facts[<l>] = <iatype>");
        facts[l] = iatype;
    } else {
        fct = openFact(deps, l, AType(){ return atype; });
        if(cdebug)println("add3: <fct>, <atype>");
        openFacts += fct;
        for(d <- deps) triggersFact[d] = triggersFact[d] ? {} + {fct};
        
    }
    fireTriggers(l);
}

void addFact(loc l, list[Tree] dependsOn, AType() getAType){
    deps = {dep@\loc | dep <- dependsOn};
    if(allDependenciesKnown(deps, facts)){
        try {
            facts[l] = getAType();
            fireTriggers(l);
            return;
        } catch TypeUnavailable(t): /* cannot yet compute type */;
    }
    fct = openFact(deps, l, getAType);
    openFacts += fct;
    for(d <- deps) triggersFact[d] = triggersFact[d] ? {} + {fct};
    fireTriggers(l);
}

void fireTriggers(loc l){
    for(req <- triggersRequirement[l] ? {}){
        if(allDependenciesKnown(req.dependsOn, facts)){
           requirementJobs += req;
           if(cdebug)println("adding requirementJob: <req.name>, <req.src>");
        }
    }
     
    for(fct <- triggersFact[l] ? {}){
        if(allDependenciesKnown(fct.dependsOn, facts)){
           try {
              addFact(fct.src, fct.getAType());
              openFacts -= fct;
           } catch TypeUnavailable(t): /* cannot yet compute type */;
        }
    }
}

// The binding of a type variable that occurs inside the scope of that type variable can be turned into a fact
void bindings2facts(map[loc, AType] bindings, loc occ){
    for(b <- bindings){
        if(isTypeVariable(b) && !facts[b]? && (!extractedFRModel.tvScopes[b]? || occ <= extractedFRModel.tvScopes[b])){
           addFact(b, bindings[b]);
           if(cdebug) println("bindings2facts, added: <b> : <bindings[b]>");
        }
    }
}
   
// Check whether a requirement is satisfied
tuple[bool ok, set[Message] messages, map[loc, AType] bindings] satisfies(Requirement req){
    bindings = ();
    try {
        req.preds();
        bindings2facts(bindings, req.src);
        return <true, {}, bindings>;
    } catch Message e: {
        return <false, {e}, bindings>;
    }
}

@doc{
.Synopsis
Get type of a tree as inferred by specified type checker

.Description
xxx
}    
AType typeof(Tree tree) {
    try {
        fct = find(tree@\loc);
        return instantiate(fct);
    } catch NoSuchKey(l): {
        throw TypeUnavailable(tree@\loc);
    }
}

AType typeof(Tree utype, Tree tree, set[IdRole] idRoles) {
   try {
     usedType = facts[utype@\loc];
     
     if(usedType has use){
        defType = lookup(extractedFRModel, usedType.use);
        res = lookup(extractedFRModel, use("<tree>", tree@\loc, facts[defType].use.scope, idRoles));
        return instantiate(facts[res]);
     } else {
        throw "typeof cannot handle <usedType>";
     }
   } catch NoKey(): {
        println("typeof: <utype@\loc>, <tree> ==\> TypeUnavailable1");
        throw TypeUnavailable(tree@\loc);
   }
}

// Check the standalone "equal" predicate that succeeds or gives error
void equal(AType given, AType expected, ErrorHandler onError){
    if(given != expected){
        throw error("<onError.msg>, expected `<AType2String(expected)>`, found `<AType2String(given)>`", onError.where);
    }
}

// Check the "equal" predicate
bool equal(AType given, AType expected){
    return given == expected;
}

// Check the standalone "unify" predicate that succeeds or gives error
void unify(AType given, AType expected, ErrorHandler onError){
    <ok, bindings1> = unify(instantiate(given), instantiate(expected), bindings);
    if(cdebug)println("unify(<given>, <expected>) =\> <ok>, <bindings1>");
    if(ok){
        bindings += bindings1;
    } else {
        iexpected = instantiate(expected);
        igiven = instantiate(given);
        throw error("<onError.msg>, expected `<AType2String(iexpected)>`, found `<AType2String(igiven)>`", onError.where);
    }
}

// Check the "unify" predicate
bool unify(AType given, AType expected){
    <ok, bindings1> = unify(instantiate(given), instantiate(expected), bindings);
    if(cdebug)println("unify(<given>, <expected>) ==\> <ok>, <bindings1>");
    if(ok){
        bindings += bindings1;
        return true;
    } else {
        return false;
    }
}

void subtype(AType small, AType large, ErrorHandler onError){
    extractedFRModel.facts = facts;
    if(!isSubtypeFun(small, large, extractedFRModel)){
        throw error("<onError.msg>, expected subtype of `<AType2String(large)>`, found `<AType2String(small)>`", onError.where);
    }
}
    
// Check the "lub" predicate
void lub(AType v, AType types, ErrorHandler onError){
    if(tvar(loc name) := v){
        itypes = instantiate(types);
        try {
            lb = getLUBFun(itypes, extractedFRModel);
            bindings = (name : lb) + bindings;
        } catch e:
             throw error("<onError.msg>, found `<AType2String(itypes)>`", onError.where); 
    }
    throw error("type variable expected, found `<v>`", onError.where); 
}

// Check the "fact" predicate
void fact(Tree t, AType atype){
        addFact(t@\loc, atype);
}
    
void error(loc src, str msg){
    throw Message::error(msg, src);
}

tuple[set[Message] messages, FRModel frmodel] validate(FRModel er,
                      bool(AType atype1, AType atype2, FRModel frm) isSubtype = noIsSubtype,
                      AType(AType atype, FRModel frm) getLUB = noGetLUB
){
    // Initialize global state
    extractedFRModel = er;
 
    facts = extractedFRModel.facts;
    openFacts = extractedFRModel.openFacts;
    bindings = ();
    openReqs = extractedFRModel.openReqs;
    triggersRequirement = ();
    triggersFact = ();
  
    requirementJobs = {};
    
    isSubtypeFun = isSubtype;
    getLUBFun = getLUB;
    
    // Initialize local state
    map[Key, Key] defs = ();
    map[loc, Overload] overloads = extractedFRModel.overloads;
    set[Use] unresolvedUses = {};
    set[Message] messages = {};
    iterations = 0;
   
    if(cdebug){
       println("overloads: <size(overloads)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
       printScopeGraph(extractedFRModel);
    }
   
    for(u <- extractedFRModel.uses){
        try {
           def = lookup(extractedFRModel, u);
           defs[u.occ] = def;
           unresolvedUses += u;
        } catch NoKey(): {
            messages += error("Undefined `<u.id>`", u.occ);
        }
    }
 
    for(Fact f <- openFacts){
       if(allDependenciesKnown(f.dependsOn, facts)){
          try {
            addFact(f.src, f.getAType());
            openFacts -= f;
            //fireTriggers(f.src);
          } catch TypeUnavailable(t): /* cannot yet compute type */;
       } else {
           for(dep <- f.dependsOn){
               if(cdebug)println("add dependency: <dep> ==\> <f>");
               triggersFact[dep] = triggersFact[dep] ? {} + {f};
           }
       }
    } 
    
    for(Define d <- extractedFRModel.defines){
       if(d.defInfo has atype){             // <+++++++
          addFact(d.defined, d.defInfo.atype);
       } else if(d.defInfo has getAType){
          addFact(d.defined, d.defInfo.dependsOn, d.defInfo.getAType);
       }
    }
  
    for(oreq <- openReqs){
       for(dep <- oreq.dependsOn){
           triggersRequirement[dep] = triggersRequirement[dep] ? {} + {oreq};
       }
    }

    for(oreq <- openReqs){
        if(allDependenciesKnown(oreq.dependsOn, facts)){
           requirementJobs += oreq;
        }
    }
           
    //solve(facts, openReqs, openFacts, unresolvedUses, requirementJobs){
    while(!(isEmpty(openFacts) && isEmpty(openReqs)) && iterations < 3){
       iterations += 1;
       
       if(cdebug){
          println("======================== iteration <iterations>");
          printState();
       }
       
       for(u <- unresolvedUses){
           def = defs[u.occ];
           if(cdebug)println("Consider unresolved use: <u>, def=<def>");
          
           if(facts[def]?){  // has type of def become available?
              fct1 = facts[def];
              deps = extractTypeDependencies(fct1);
              if(cdebug)println("use is defined as: <fct1>, deps: <deps>");
              if(allDependenciesKnown(deps, facts)){ 
                 addFact(u.occ, instantiate(fct1));
                 unresolvedUses -= {u};
                 if(cdebug)println("Resolved use: <u>");
              }
           } else {
              if(cdebug) println("not yet known: <def>");
           }
      }

       // eliminate overloads for which argument types are known
       for(ovlKey <- overloads){
          ovl = overloads[ovlKey];
          if(all(p <- ovl.args, facts[p]?)){
              try {
                t = ovl.resolve();
                addFact(ovlKey, t);
                bindings2facts(bindings, ovl.src); 
              } catch TypeUnavailable(t): {
                continue;
              } catch Message e: {
                messages += e;
              }
              overloads = delete(overloads, ovlKey);
          }
       }  
       
       // Check open requirements when they are known
       // Sort to force bottom-up evaluation
       for(oreq <- sort(requirementJobs, bool(Requirement a, Requirement b) { return a.src < b.src; })){
          if(cdebug)println("\nchecking `<oreq.name>`: <oreq.src>\n<oreq>");
          if(allDependenciesKnown(oreq.dependsOn, facts)){ 
             if(cdebug)println("checking `<oreq.name>`: dependencies are available");  
             try {       
                 <ok, messages1, bindings1> = satisfies(oreq); 
                 if(cdebug)println("ok=<ok>, <messages1>, <bindings1>");
                 messages += messages1;
                 if(ok){
                    if(cdebug)println("checking `<oreq.name>`: bindings: <bindings1>");
                    for(tv <- domain(bindings1), f <- triggersFact[tv] ? {}){
                        if(allDependenciesKnown(f.dependsOn, facts)){
                            try {
                                if(cdebug)println("checking `<oreq.name>`: adding bound fact: <f>");
                                addFact(f.src, f.getAType());
                                openFacts -= {f};
                            } catch TypeUnavailable(t): /* cannot yet compute type */;
                        }
                    }
                    
                    if(cdebug)println("checking `<oreq.name>`: deleting1");
                    openReqs -= {oreq};
                 } else {
                     if(cdebug)println("!ok: <messages1>");
                     if(cdebug)println("checking `<oreq.name>`: deleting2");
                     openReqs -= oreq;
                 }
             } catch TypeUnavailable(t):
                println("checking `<oreq.name>`: dependencies not yet available");
          } else {
            println("checking `<oreq.name>`: dependencies not yet available");
          }
      }
    }   
   
    if(size(overloads) > 0){
      for(l <- overloads){
          ovl = overloads[l];
          args = overloads[l].args;
          messages += error("Overloaded operator <ovl.name> could not be resolved for <for(int i <- index(args)){><facts[args[i]]? ? "`<AType2String(facts[args[i]])>`" : "unknown"><i < size(args)-1 ? "," : ""> <}>", ovl.src );
      }
    }
   
    messages += { error("Invalid <req.name>", req.src) | req <- openReqs};
   
    if(cdebug){
       println("------");
       println("iterations: <iterations>; overloads: <size(overloads)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
       printState();
       
       println("------");
       if(isEmpty(messages) && isEmpty(openReqs) && isEmpty(openFacts)){
          println("No type errors found");
       } else {
          println("Errors:");
          for(msg <- messages){
              println(msg);
          }
          if(!isEmpty(openReqs)) println("*** <size(openReqs)> unresolved requirements ***");
          if(!isEmpty(openFacts)) println("*** <size(openFacts)> open facts ***");
       }
    }
    er.facts = facts;
    return <filterMostPrecise(messages), er>;
}

rel[loc, loc] getUseDef(FRModel frm){
    res = {};
    for(Use u <- frm.uses){
        try {
           res += <u.occ, lookup(frm, u)>;
        } catch NoKey(): {
            ;// ignore it
        }
    };
    return res;
}

set[str] getVocabulary(FRModel frm)
    = {d.id | Define d <- frm.defines};

map[loc, AType] getFacts(FRModel frm)
    = frm.facts;

