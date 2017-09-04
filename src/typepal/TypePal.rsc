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

FRModel getFRModel(){
    return extractedFRModel[facts=facts];
}

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
    = UnspecifiedIsSubType(AType atype1, AType atype2)
    | UnspecifiedGetLUB(AType atype1, AType atype2)
    | UndefinedLUB(AType atype1, AType atype2)
    | TypeUnavailable(Key k)
    ;

// defaults for isSubType and getLUB
bool noIsSubType(AType atype1, AType atype2) {
    throw UnspecifiedIsSubType(atype1, atype2);
}

AType noGetLUB(AType atype1, AType atype2){
    throw UnspecifiedGetLUB(atype1, atype2);
}

bool(AType atype1, AType type2) isSubTypeFun = noIsSubType;
AType(AType atype1, AType atype2) getLUBFun = noGetLUB;

// Error handling

str intercalateAnd(list[str] strs){
    switch(size(strs)){
      case 0: return "";
      case 1: return strs[0];
      default: 
              return intercalate(", ", strs[0..-1]) + " and " + strs[-1];
      };
}

void reportError(Tree t, str msg, list[Tree] found){
    throw error("<msg>, found <intercalateAnd(["`<AType2String(typeof(f))>`" | f <- found])>", t@\loc);
}

set[Message] filterMostPrecise(set[Message] messages)
    = { msg | msg <- messages, !any(msg2 <- messages, surrounds(msg, msg2) /*|| 
                                                      (msg.msg == msg2.msg && msg.at.begin.line > msg2.at.begin.line)*/) };
bool surrounds (Message msg1, Message msg2){
    // TODO: return msg1.at > msg2.at should also work but does not.
    return msg1.at.offset <= msg2.at.offset && msg1.at.offset + msg1.at.length > msg2.at.offset + msg2.at.length;
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
        case lub(atype1, atype2) => getLUBFun(substitute(atype1), substitute(atype2))
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

bool addFact(loc l, AType atype){
    if(cdebug)println("\naddFact1: <l>, <atype>, 
                      '\ttrigF: <triggersFact[l]?{}>, 
                      '\ttrigR: <triggersRequirement[l]?{}>");
  
    deps = extractTypeDependencies(atype);
    if(allDependenciesKnown(deps, facts)){
        iatype = instantiate(atype);
        if(cdebug)println("\tadd2: facts[<l>] = <iatype>");
        facts[l] = iatype;
        fireTriggers(l);
        return true;
    } else {
        fct = openFact(l, deps, AType(){ return atype; });
        if(cdebug)println("\tadd3: <fct>, <atype>");
        openFacts += fct;
        for(d <- deps) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
        return false;
    }
}

bool addFact(fct:openFact(loc src, set[loc] dependsOn,  AType() getAType)){
    if(cdebug)println("addFact2: <fct>");
    if(allDependenciesKnown(dependsOn, facts)){
        try {
            facts[src] = getAType();
            fireTriggers(src);
            return true;
        } catch TypeUnavailable(t): /* cannot yet compute type */;
    }
    openFacts += fct;
    for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
    fireTriggers(src);
    return false;
}

bool addFact(fct:openFact(set[loc] defines, set[loc] dependsOn, list[AType()] getATypes)){
    if(cdebug)println("addFact3: <fct>");
    if(allDependenciesKnown(dependsOn, facts)){
        try {    
            tp =  (getATypes[0]() | getLUBFun(it, gat()) | gat <- getATypes[1..]);    
            for(def <- defines){ facts[def] = tp;  }
            for(def <- defines) { fireTriggers(def); }
            if(cdebug)println("\taddFact3: lub computed: <tp> for <defines>");
            return true;
        } catch TypeUnavailable(t): /* cannot yet compute type */;
    }
    
    // try to partially compute the lub;
    knownTypes = ();
    solve(knownTypes){
        AType currentLub;
        for(int i <- index(getATypes)){
            try {
                knownTypes[i] = getATypes[i]();
                currentLub = currentLub? ? getLUBFun(currentLub, knownTypes[i]) : knownTypes[i];
            } catch TypeUnavailable(t): /*println("unavailable: <i>")*/;
        }
        
        if(currentLub?){
            for(def <- defines){ facts[def] = currentLub;  }
            for(def <- defines) { 
                try fireTriggers(def, protected=false); 
                catch TypeUnavailable(t):
                    facts = delete(facts, def);
            }
        }
    }
    if(size(knownTypes) == size(getATypes))
        return true;
    
    // last resort
    openFacts += fct;
    if(cdebug)println("\taddFact3: adding dependencies: <dependsOn>");
    for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
    for(def <- defines) fireTriggers(def);
    return false;
}

default void addFact(Fact fct) {
    throw "Cannot handle <fct>";
}

void fireTriggers(loc l, bool protected=true){
    if(cdebug) println("\tfireTriggers: <l>");
    
    for(fct <- triggersFact[l] ? {}){
        if(allDependenciesKnown(fct.dependsOn, facts)){
           try {
              if(cdebug) println("\tfireTriggers: adding fact: <fct>");
              openFacts -= fct;
              addFact(fct);
           } catch TypeUnavailable(Key t): {
                  /* cannot yet compute type */;
                  if(!protected){
                     throw TypeUnavailable(t);
                  }
              }
        }
    }
    
    for(req <- triggersRequirement[l] ? {}){
        if(allDependenciesKnown(req.dependsOn, facts)){
           requirementJobs += req;
           if(cdebug)println("\tfireTriggers: adding requirementJob: <req.name>, <req.src>");
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

// The "run-time" functions that can be called from requirements and calculators

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

AType typeof(tvar(loc l)){
    try {
        tp = facts[l];
        return tp;
    } catch NoSuchKey(k): {
        throw TypeUnavailable(l);
    }
}

AType typeof(Tree utype, Tree tree, set[IdRole] idRoles) {
   try {
     usedType = facts[utype@\loc];
     
     if(usedType has use){
        definedType = lookup(extractedFRModel, usedType.use);
        res = lookup(extractedFRModel, use("<tree>", tree@\loc, facts[definedType].use.scope, idRoles));
        return instantiate(facts[res]);
     } else {
        throw "typeof cannot handle <usedType>";
     }
   } catch NoKey(): {
        println("typeof: <utype@\loc>, <tree> ==\> TypeUnavailable1");
        throw TypeUnavailable(tree@\loc);
   }
}

// The "equal" predicate that succeeds or gives error
void equal(AType given, AType expected, ErrorHandler onError){
    if(given != expected){
        throw error("<onError.msg>, expected `<AType2String(expected)>`, found `<AType2String(given)>`", onError.where);
    }
}

// Check the "equal" predicate
bool equal(AType given, AType expected){
    return given == expected;
}

// The "unify" predicate that succeeds or gives error
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

// The "subtype" predicate
void subtype(AType small, AType large, ErrorHandler onError){
    extractedFRModel.facts = facts;
    if(!isSubTypeFun(small, large)){
        throw error("<onError.msg>, expected subtype of `<AType2String(large)>`, found `<AType2String(small)>`", onError.where);
    }
}

// The "comparable" predicate
void comparable(AType atype1, AType atype2, ErrorHandler onError){
    extractedFRModel.facts = facts;
    if(!(isSubTypeFun(atype1, atype2) || isSubTypeFun(atype2, atype1))){
        throw error("<onError.msg>, `<AType2String(atype1)>` and `<AType2String(atype2)>` are not comparable", onError.where);
    }
}

// The "fact" assertion
void fact(Tree t, AType atype){
        addFact(t@\loc, atype);
}

// The "error" assertion 
void error(loc src, str msg){
    throw Message::error(msg, src);
}

/*
 *  validate: validates an extracted FRModel via constraint solving
 *  
 */

FRModel validate(FRModel er,
                      bool(AType atype1, AType atype2) isSubType = noIsSubType,
                      AType(AType atype1, AType atype2) getLUB = noGetLUB,
                      set[IdRole] mayBeOverloaded = {},
                      bool debug = false
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
    
    isSubTypeFun = isSubType;
    getLUBFun = getLUB;
    cdebug = debug;
    
    // Initialize local state
    map[Key, Key] defs = ();
    map[loc, Calculator] calculators = extractedFRModel.calculators;
    set[Use] unresolvedUses = {};
    set[Message] messages = {};
    iterations = 0;
   
    if(cdebug){
       println("calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
       printFRModel(extractedFRModel);
    }
   
    if(cdebug) println("==== lookup uses ====");
    for(u <- extractedFRModel.uses){
        try {
           def = lookup(extractedFRModel, u);
           defs[u.occ] = def;
           unresolvedUses += u;
           //println("Handled: <u>");
        } catch NoKey(): {
            //messages += error("Undefined `<getId(u)>`", u.occ);
            unresolvedUses += u;
            //println("Not handled: <u>");
        } catch AmbiguousDefinition(Key scope, str id, set[IdRole] idRoles, set[Key] definitions):{
            if(idRoles <= mayBeOverloaded){
                unresolvedUses += u;
            } else {
                messages += {error("Double declaration", d) | d <- definitions} + error("Undefined `<getId(u)>`due to double declaration", u.occ);
            }
        }
    }
    
    if(cdebug) println("==== handle defines ====");
    for(Define d <- extractedFRModel.defines){
       if(d.defInfo is noDefInfo){
       ;
       } else if(d.defInfo has atype){             // <+++++++ refactor
          addFact(d.defined, d.defInfo.atype);
       } else if(d.defInfo has getAType){
          addFact(openFact(d.defined, d.defInfo.dependsOn, d.defInfo.getAType));
       } else if(d.defInfo has getATypes){
          addFact(openFact(d.defInfo.defines, d.defInfo.dependsOn, d.defInfo.getATypes));
       } else {
            throw "Cannot handle <d>";
       }
    }
 
    if(cdebug) println("==== consider open facts ====");
    for(Fact f <- openFacts){
        if(addFact(f)){
            openFacts -= f;
        }
    } 
    
    if(cdebug) println("==== handle open requirements ===");
    for(oreq <- openReqs){
       for(dep <- oreq.dependsOn){
           triggersRequirement[dep] = (triggersRequirement[dep] ? {}) + {oreq};
       }
    }

    for(oreq <- openReqs){
        if(allDependenciesKnown(oreq.dependsOn, facts)){
           requirementJobs += oreq;
        }
    }
    if(cdebug){
        println("Fact triggers:");
        for(dep <- triggersFact){
            println("<dep> triggers\n\t<triggersFact[dep]>\n");
        }
        
        println("Requirement triggers:");
        for(dep <- triggersRequirement){
            println("<dep> triggers\n\t<triggersRequirement[dep]>\n");
        }
    }
           
    //solve(facts, openReqs, openFacts, unresolvedUses, requirementJobs){
    while(!(isEmpty(openFacts) && isEmpty(openReqs) && isEmpty(calculators)) && iterations < 4){
       iterations += 1;
       
       if(cdebug){
          println("======================== iteration <iterations>");
          printState();
       }
       
        for(Fact f <- openFacts){
            if(addFact(f)){
                openFacts -= f;
            }
        }
       
       for(u <- unresolvedUses){
           try {
               Key def;
               if(defs[u.occ]?){
                    def = defs[u.occ];
               } else {
                    try {
                        def = lookup(extractedFRModel, u);
                        defs[u.occ] = def;
                    } catch AmbiguousDefinition(Key scope, str id, set[IdRole] idRoles, set[Key] definitions):{
                        if(all(d <- definitions, facts[d]?)){
                            addFact(u.occ, overloadedType({<d, facts[d]> | d <- definitions}));
                            unresolvedUses -= u;
                            continue;
                        }
                    }
               }
              
               if(cdebug)println("Consider unresolved use: <u>, def=<def>");
              
               if(facts[def]?){  // has type of def become available?
                  fct1 = facts[def];
                  deps = extractTypeDependencies(fct1);
                  if(cdebug)println("use is defined as: <fct1>, deps: <deps>");
                  if(allDependenciesKnown(deps, facts)){ 
                     addFact(u.occ, instantiate(fct1));
                     unresolvedUses -= u;
                     if(cdebug)println("Resolved use: <u>");
                  }
               } else {
                  if(cdebug) println("not yet known: <def>");
               }
           } catch NoKey(): {
                if(cdebug) println("not yet known: <u>");;
           }
      }
      
       // eliminate calculators for which argument types are known
       for(calcKey <- calculators){
          calc = calculators[calcKey];
          if(isEmpty(calc.dependsOn) || all(dep <- calc.dependsOn, facts[dep]?)){
              try {
                t = calc.calculator();
                addFact(calcKey, t);
                bindings2facts(bindings, calc.src); 
              } catch TypeUnavailable(t): {
                continue;
              } catch Message e: {
                messages += e;
              }
              calculators = delete(calculators, calcKey);
          }
       }  
       
       // Check open requirements when they are known
       // Sort to force bottom-up evaluation
       for(oreq <- sort(requirementJobs, bool(Requirement a, Requirement b) { return a.src < b.src; })){
          if(cdebug)println("\nchecking `<oreq.name>`: <oreq.src>\n\t<oreq>");
          if(allDependenciesKnown(oreq.dependsOn, facts)){ 
             if(cdebug)println("\tchecking `<oreq.name>`: dependencies are available");  
             try {       
                 <ok, messages1, bindings1> = satisfies(oreq); 
                 if(cdebug)println("\tok=<ok>, <messages1>, <bindings1>");
                 messages += messages1;
                 if(ok){
                    if(cdebug)println("\tchecking `<oreq.name>`: bindings: <bindings1>");
                    for(tv <- domain(bindings1), f <- triggersFact[tv] ? {}){
                        if(allDependenciesKnown(f.dependsOn, facts)){
                            try {
                                if(cdebug)println("\tchecking `<oreq.name>`: adding bound fact: <f>");
                                addFact(f.src, f.getAType());
                                openFacts -= {f};
                            } catch TypeUnavailable(t): /* cannot yet compute type */;
                        }
                    }
                    
                    if(cdebug)println("\tchecking `<oreq.name>`: deleting1");
                    openReqs -= oreq;
                    requirementJobs -= oreq;
                 } else {
                     if(cdebug)println("\t!ok: <messages1>");
                     if(cdebug)println("\tchecking `<oreq.name>`: deleting2");
                     openReqs -= oreq;
                     requirementJobs -= oreq;
                 }
             } catch TypeUnavailable(t):
                println("checking `<oreq.name>`: dependencies not yet available");
          } else {
            println("\tchecking `<oreq.name>`: dependencies not yet available");
          }
      }
    } 
    
    for(u <- unresolvedUses) {
        if (defs[u.occ]?) {
          if (!(facts[defs[u.occ]]?)) 
            messages += { error("Unresolved type for `<u.id>`", u.occ)};
          else   
            messages += { error("Unresolved dependencies for `<u.id>`: <extractTypeDependencies(facts[defs[u.occ]])>", u.occ) };
        }
        else 
          messages += { error("Undefined `<u.id>`", u.occ) };  
    }
   
    if(size(calculators) > 0){
      for(l <- calculators){
          calc = calculators[l];
          deps = calculators[l].dependsOn;
          messages += error("Type of <calc.name> could not be computed for <for(int i <- index(deps)){><facts[deps[i]]? ? "`<AType2String(facts[deps[i]])>`" : "`unknown type`"><i < size(deps)-1 ? "," : ""> <}>", calc.src );
      }
    }
   
    messages += { error("Invalid <req.name>", req.src) | req <- openReqs};
   
    if(cdebug){
       println("------");
       println("iterations: <iterations>; calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
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
    er.messages = filterMostPrecise(messages);
    return er;
}

rel[loc, loc] getUseDef(FRModel frm){
    res = {};
    for(Use u <- frm.uses){
        try {
           res += <u.occ, lookup(frm, u)>;
        } catch NoKey(): {
            ;// ignore it
        } catch AmbiguousDefinition(_,_,_,_):{
            ;// ignore it
        }
    };
    return res;
}

set[str] getVocabulary(FRModel frm)
    = {d.id | Define d <- frm.defines};

map[loc, AType] getFacts(FRModel frm)
    = frm.facts;

set[Message] getMessages(FRModel frm)
    = frm.messages;
