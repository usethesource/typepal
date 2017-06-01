module Constraints

import Set; 
import Node;
import Map;
import IO;
import List; 
import ParseTree;
extend ScopeGraph;
extend ExtractScopesAndConstraints;
import String;
import Message;

bool cdebug = true;

bool noIsSubtype(AType atype1, AType atype2, ScopeGraph sg) {
    throw "isSubType not defined but used for: <atype1>, <atype2>";
}

AType noGetLUB(AType atype, ScopeGraph sg){
    throw "getLUB not defined but used for: <atype>";
}

// Substitute top-level type variables in a type first using bindings, then facts
AType substitute(AType atype, map[loc, AType] bindings, map[loc, AType] facts, ScopeGraph sg)
    = substituteUsingBindingsAndFacts(atype, bindings, facts, sg);
   
AType substituteUsingBindingsAndFacts(AType atype, map[loc, AType] bindings, map[loc, AType] facts, ScopeGraph sg){
    if(typeof(loc src) := atype || tvar(loc src) := atype){
       if(bindings[src]?){
          fct = bindings[src];
          if(isTypeofOrTVar(fct)){
             return substituteUsingBindingsAndFacts(fct, bindings, facts, sg);
          }
          return substituteUsingFacts(fct, facts, sg);
        }
    } else if(typeof(loc scope, loc src, str id, set[IdRole] idRoles) := atype){
       //println("substituteUsingBindingsAndFacts: <scope>, <src>, <id>");
       if(bindings[src]?){
          try {
            return lookup(sg, use(id, src, scope, idRoles));
          } catch noKey:
            return atype;
        }
    }
    return isTypeofOrTVar(atype) ? substituteUsingFacts(atype, facts, sg) : atype;
}

AType substituteUsingFacts(AType atype, map[loc, AType] facts, ScopeGraph sg){
    if(typeof(loc src) := atype || tvar(loc src) := atype){
       if(facts[src]?){
          fct = facts[src];
          if(isTypeofOrTVar(fct)){
             return substituteUsingFacts(fct, facts, sg);
          }
          while(fct has use){
          
            defType = lookup(sg, fct.use); 
            fct1 = facts[defType];
            if(fct1 != fct){
                fct = fct1;
            } else {
                break;
            }
          }
          return fct;
        }
    } else if(typeof(loc utype, loc src, str id, set[IdRole] idRoles) := atype){
       println("\n@@@ substituteUsingFacts: <utype>, <facts[utype]?> <src> <facts[src]?>, <id>");
       if(facts[utype]?){
          println("uType: <utype>, <facts[utype]>\nsrc: <src> <facts[src]?"undefined">, <id>");
          usedType = facts[utype];
          println("usedType: <usedType>");
          try {
            if(usedType has use){
                defType = lookup(sg, usedType.use);
                println("defType = <defType>");
                println("facts[defType] = <facts[defType]>");
                res = lookup(sg, use(id, src, facts[defType].use.scope, idRoles));
                println("returns <res>, <facts[res]>");
                return substituteUsingFacts(facts[res], facts, sg);
            } else {
                throw "substituteUsingFacts cannot handle <usedType>";
            }
          } catch noKey: {
                //println("returns (noKey) <atype>");
                return atype;
            }
        }
    }
    return atype;
}

// Recursively instantiate all type variables in a type
AType instantiate(AType atype, map[loc, AType] bindings, map[loc, AType] facts, ScopeGraph sg){
  return
      visit(atype){
        case to: typeof(loc src): {
            insert substitute(to, bindings, facts, sg);
        }
        case to: typeof(loc scope, loc src, str id, set[IdRole] idRoles): {
            insert substitute(to, bindings, facts, sg);
        }
        case tv: tvar(loc src): {
            insert substitute(tv, bindings, facts, sg);
        }
      };
}

// Instantiate facts    
//Fact instantiate(Fact fct, map[loc, AType] bindings, map[loc, AType] facts, ScopeGraph sg)
//    = visit(fct) { case AType atype => instantiate(atype, bindings, facts, sg) };

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

set[Message] filterMostPrecise(set[Message] messages)
    = { msg | msg <- messages, !any(msg2 <- messages, surrounds(msg, msg2) || 
                                                      (msg.msg == msg2.msg && msg.at.begin.line > msg2.at.begin.line)) };


bool surrounds (Message msg1, Message msg2){
    // TODO: return msg1.at > msg2.at should also work but does not.
    return msg1.at.offset < msg2.at.offset && msg1.at.offset + msg1.at.length > msg2.at.offset + msg2.at.length;
}

ScopeGraph extractedRequirements;
map[loc, AType] facts = ();
set[Fact] openFacts = {};
map[loc, AType] bindings = ();
rel[loc, Requirement] triggersRequirement = {};
rel[loc, Requirement] tvtriggersRequirement = {};
   
rel[loc, Fact] triggersFact = {};
rel[loc, Fact] tvtriggersFact = {};

set[Requirement] requirementJobs = {};

// defaults for iisSubtype and getLUB
bool(AType atype1, AType atype2, ScopeGraph sg) isSubtypeFun = noIsSubtype;
AType(AType atype, ScopeGraph sg) getLUBFun = noGetLUB;


 void addFact(loc l, AType atype){
     if(cdebug)println("\naddFact: <l>, <atype>, <triggersFact[l]>, <triggersRequirement[l]>");
   
     if(typeof(loc other) := atype){// || tvar(loc other) := atype){
     // TODO: support typeof(_,_,_) as well
        if(facts[other]?){
           if(cdebug)println("add: facts[<l>] = <facts[other]>");
           facts[l] = facts[other];
        } else {
           if(other != l){
              fct = openFact({other}, {}, l, AType() { return atype; });
              if(cdebug)println("add1: <fct>");
              openFacts += fct;
              triggersFact += <other, fct>;
           }
        }
     } else {
        <deps, tvvars> = extractTypeDependencies(atype);
        println("deps=<deps>, tvvars=<tvvars>");
        if(allDependenciesKnown(deps, tvvars, facts)){
            iatype = instantiate(atype, (), facts, extractedRequirements);
            if(cdebug)println("add2: facts[<l>] = <iatype>");
            facts[l] = iatype;
        } else {
            fct = openFact(deps, tvvars, l, AType(){ return atype; });
            if(cdebug)println("add3: <fct>");
            openFacts += fct;
            for(d <- deps) triggersFact += <d, fct>;
        }
     }
     
     for(req <- triggersRequirement[l]){
         if(allDependenciesKnown(req.dependsOn, req.dependsOnTV, facts)){
           requirementJobs += req;
           if(cdebug)println("adding requirementJob: <req.name>, <req.src>");
         }
     }
     
     for(fct <- triggersFact[l]){
         if(allDependenciesKnown(fct.dependsOn, fct.dependsOnTV, facts)){
            addFact(fct.src, fct.makeType());
            openFacts -= fct;
         }
      }
}

AType typeof(Tree t) = bindings[t@\loc] ? facts[t@\loc];

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
    <ok, bindings1> = unify(given, expected, bindings);
    println("unify(<given>, <expected>) =\> <ok>, <bindings1>");
    if(ok){
        bindings += bindings1;
    } else {
        throw error("<onError.msg>, expected `<AType2String(expected)>`, found `<AType2String(given)>`", onError.where);
    }
}

// Check the "unify" predicate
bool unify(AType given, AType expected){
    <ok, bindings1> = unify(given, expected, bindings);
    if(ok){
        bindings += bindings1;
        return true;
    } else {
        return false;
    }
}

void subtype(AType small, AType large, ErrorHandler onError){
    //ismall = instantiate(small, bindings, facts, extractedRequirements);
    //ilarge = instantiate(large, bindings, facts, extractedRequirements);
    //println("small = <small>");
    //println("ismall = <ismall>");
    //println("large = <large>");
    //println("ilarge = <ilarge>");
    extractedRequirements.facts = facts;
    if(!isSubtypeFun(small, large, extractedRequirements)){
        throw error("<onError.msg>, expected subtype of `<AType2String(large)>`, found `<AType2String(small)>`", onError.where);
    }
}
    
// Check the "lub" predicate
void lub(AType v, AType types, ErrorHandler onError){
    if(tvar(loc name) := v){
        itypes = instantiate(types, bindings, facts, extractedRequirements);
        try {
            lb = getLUBFun(itypes, extractedRequirements);
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

set[Message] validate(ScopeGraph er,
                      bool(AType atype1, AType atype2, ScopeGraph sg) isSubtype = noIsSubtype,
                      AType(AType atype, ScopeGraph sg) getLUB = noGetLUB
){
   extractedRequirements = er;
   overloads = extractedRequirements.overloads;
   facts = extractedRequirements.facts;
   openFacts = extractedRequirements.openFacts;
   openReqs = extractedRequirements.openReqs;
   tvScopes = extractedRequirements.tvScopes;
   
   map[Key, Key] defs = ();
   
   triggersRequirement = {};
   tvtriggersRequirement = {};
   
   triggersFact = {};
   tvtriggersFact = {};
   
   set[Use] unresolvedUses = {};
   requirementJobs = {};
   
   isSubtypeFun = isSubtype;
   getLUBFun = getLUB;
   
   if(cdebug){
      println("overloads: <size(overloads)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
      printScopeGraph(extractedRequirements);
   }
   
   set[Message] messages = {};
   iterations = 0;
   
   void printState(){
    println("facts:");
        for(Key fact <- facts){
            println("\t<fact>: <facts[fact]>");
        }
    //println("triggersFact:");
    //    for(<loc k, f> <- triggersFact){
    //        println("<k> ===\> <f.src>, <f.atype>");
    //    }
    //println("tvtriggersRequirement:");
    //    for(<loc k, r> <- tvtriggersRequirement){
    //        println("<k> ===\> <r.name>, <r.src>");
    //    }
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
            for(atype <- rq.dependsOnTV){
                println("\t  dependsOnTV: <atype>");
            }
            //println("\t  preds:");
            //for(pred <- rq.preds) println("\t    <pred>");
        }
   }
   
   // The binding of a type variable that occurs inside the scope of that type variable can be turned into a fact
   void bindings2facts(map[loc, AType] bindings, loc occ){
        for(b <- bindings){
            if(cdebug && !facts[b]? && tvScopes[b]?) println("Consider <b>, <bindings[b]>, <isGlobalTypeVar(b)>, <!facts[b]?>, <occ>, <tvScopes[b]>, <occ <= tvScopes[b]>");
            if(isGlobalTypeVar(b) && !facts[b]? && (occ <= tvScopes[b])){
               addFact(b, bindings[b]);
               if(cdebug) println("Adding type var: <b> : <bindings[b]>");
            }
        }
    }
   
    // Check whether all predicates of a requirement are satisfied
    tuple[bool ok, set[Message] messages, map[loc, AType] bindings] 
        satisfies(Requirement req, map[loc, loc] tvScopes){
        preds = req.preds;
        req_messages = {};
        bindings = ();
        try {
            preds();
        } catch Message e: {
            return <false, {e}, bindings>;
        }
        bindings2facts(bindings, req.src);
        return <true, req_messages, bindings>;
    }
    
    extractedRequirements.defines = 
        visit(extractedRequirements.defines) {
        case useType(Use u): { 
            try {
                k = lookup(extractedRequirements, u);
                println("useType<u> ==\> <k>");
                insert typeof(k);  
            } catch noKey:
                messages += error("Undefined `<u.id>`", u.occ);
         }
    }
    
    extractedRequirements.facts = 
        visit(extractedRequirements.facts) {
        case useType(Use u): { 
            try
                insert typeof(lookup(extractedRequirements, u));  
            catch noKey:
                messages += error("Undefined `<u.id>`", u.occ);
         }
    }
    
    extractedRequirements.overloads = 
        visit(extractedRequirements.overloads) {
        case useType(Use u): { 
            try
                insert typeof(lookup(extractedRequirements, u));  
            catch noKey:
                messages += error("Undefined `<u.id>`", u.occ);
         }
    }
    extractedRequirements.openFacts = 
        visit(extractedRequirements.openFacts) {
        case useType(Use u): { 
            try
                insert typeof(lookup(extractedRequirements, u));  
            catch noKey:
                messages += error("Undefined `<u.id>`", u.occ);
         }
    }
    
    extractedRequirements.openReqs = 
        visit(extractedRequirements.openReqs) {
        case useType(Use u): { 
            try
                insert typeof(lookup(extractedRequirements, u));  
            catch noKey:
                messages += error("Undefined `<u.id>`", u.occ);
         }
    }
    
    for(u <- extractedRequirements.uses){
        try {
           //println("u = <u>");
           def = lookup(extractedRequirements, u);
           //println("def = <def>");
           defs[u.occ] = def;
           unresolvedUses += u;
        } catch noKey: {
            //println("UNDEFINED");
            messages += error("Undefined `<u.id>`", u.occ);
        }
    }
 
   for(Fact f <- openFacts){
       if(allDependenciesKnown(f.dependsOn, f.dependsOnTV, facts)){
          addFact(f.src, f.makeType());
          openFacts -= f;
       } else {
           for(dep <- f.dependsOn){
               if(cdebug)println("add dependency: <dep> ==\> <f>");
               triggersFact += <dep, f>;
           }
           for(tvdep <- f.dependsOnTV){
               tvtriggersFact += <tvdep, f>;
           }
       }
   } 
    
    for(Define d <- extractedRequirements.defines){
       if(d.defInfo has atype){             // <+++++++
          addFact(d.defined, d.defInfo.atype);
       }
    }
  
    for(oreq <- openReqs){
       for(dep <- oreq.dependsOn){
           triggersRequirement += {<dep, oreq>};
       }
       for(tvdep <- oreq.dependsOnTV){
           tvtriggersRequirement += {<tvdep, oreq>};
       }
    }

    for(oreq <- openReqs){
        if(allDependenciesKnown(oreq.dependsOn, oreq.dependsOnTV, facts)){
           requirementJobs += oreq;
        }
    }
           
    solve(facts, openReqs, openFacts, unresolvedUses, requirementJobs){
    //while(!(isEmpty(openFacts) && isEmpty(openReqs)) && iterations < 10){
       iterations += 1;
       
       if(cdebug){
          println("======================== iteration <iterations>");
          printState();
       }
       
       for(u <- unresolvedUses){
           if(cdebug)println("Consider use: <u>");
           def = defs[u.occ];
           if(facts[def]?){  // has type of def become available?
              fct1 = facts[def];
              <deps, tvdeps> = extractTypeDependencies(fct1);
              if(cdebug)println("fact: <fct1>, deps: <deps>, <tvdeps>");
              if(allDependenciesKnown(deps, tvdeps, facts)){ 
                 addFact(u.occ, instantiate(fct1, (), facts, extractedRequirements));
                 unresolvedUses -= {u};
                 if(cdebug)println("Resolved use: <u>");
              }
           } else {
              if(cdebug) println("not yet known: <def>");
           }
      }
       
       // eliminate overloads for which argument types are known
       for(ovlKey <- extractedRequirements.overloads){
          ovl = extractedRequirements.overloads[ovlKey];
          args = ovl.args;
          if(all(p <- args, facts[p]?)){
              try {
                t = ovl.resolve();
                addFact(ovlKey, t);
                bindings2facts(bindings, ovl.src);
                overloads = delete(overloads, ovlKey);
              } catch Message e: {
                messages += e;
              }
          }
       }  
       
       // Check open requirements when their predicate can be fully instantiated
       for(oreq <- requirementJobs){
          if(cdebug)println("\nchecking: <oreq.name>, <oreq.src>\n<oreq>");
          if(allDependenciesKnown(oreq.dependsOn, oreq.dependsOnTV, facts)){          
             <ok, messages1, bindings1> = satisfies(oreq, tvScopes); 
             if(cdebug)println("<ok>, <messages1>, <bindings1>");
             messages += messages1;
             if(ok){
                if(cdebug)println("reqs: bindings: <bindings1>");
                tvars = domain(bindings1);
                treqs = tvtriggersRequirement[tvars];
                tfacts = triggersFact[tvars];
                for(r <- treqs){
                    requirementJobs += { r };
                }
                for(f <- tfacts){
                    if(cdebug)println("reqs, adding bound fact: <instantiate(f, bindings1, facts, extractedRequirements)>");
                    fct = instantiate(f, bindings1, facts, extractedRequirements);
                    addFact(f.src, fct.makeType()) ;
                }
                
                if(cdebug)println("deleting1: <oreq.name>, <oreq.src>\n<oreq>");
                //iprintln(openReqs);
                openReqs -= {oreq};
                //println("after deleting <oreq>:");
                //iprintln(openReqs);
                
             } else {
                 if(cdebug)println("!ok: <messages1>");
                 if(cdebug)println("deleting2: <oreq.name>, <oreq.src>");
                 openReqs -= oreq;
             }
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
   return filterMostPrecise(messages);
}

