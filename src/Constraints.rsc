module Constraints

import Set; 
import Node;
import Map;
import IO;
import List; 
import ParseTree;
extend ScopeGraph;
extend ExtractScopesAndConstraints;
import Type;
import String;
import Message;

bool cdebug = true;

// Substitute top-level type variables in a type first using bindings, then facts
AType substitute(AType atype, map[loc, AType] bindings, map[loc, AType] facts)
    = substituteUsingBindingsAndFacts(atype, bindings, facts);
   
AType substituteUsingBindingsAndFacts(AType atype, map[loc, AType] bindings, map[loc, AType] facts){
    if(typeof(loc src) := atype || tvar(loc src) := atype){
       if(bindings[src]?){
          fct = bindings[src];
          if(isTypeofOrTVar(fct)){
             return substituteUsingBindingsAndFacts(fct, bindings, facts);
          }
          return substituteUsingFacts(fct, facts);
        }
    }
    return isTypeofOrTVar(atype) ? substituteUsingFacts(atype, facts) : atype;
}

AType substituteUsingFacts(AType atype, map[loc, AType] facts){
    if(typeof(loc src) := atype || tvar(loc src) := atype){
       if(facts[src]?){
          fct = facts[src];
          if(isTypeofOrTVar(fct)){
             return substituteUsingFacts(fct, facts);
          }
          return fct;
        }
    }
    return atype;
}

// Recursively instantiate all type variables in a type
AType instantiate(AType atype, map[loc, AType] bindings, map[loc, AType] facts){
  return
      visit(atype){
        case to: typeof(loc src): {
            insert substitute(to, bindings, facts);
        }
        case tv: tvar(loc src): {
            insert substitute(tv, bindings, facts);
        }
      };
}

// Instantiate requirements
Requirement instantiate(Requirement req, map[loc, AType] bindings, map[loc, AType] facts)
    = visit(req) { case AType atype => instantiate(atype, bindings, facts) };

// Instantiate facts    
Fact instantiate(Fact fct, map[loc, AType] bindings, map[loc, AType] facts)
    = visit(fct) { case AType atype => instantiate(atype, bindings, facts) };

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
   
    c1 = getName(t1); c2 = getName(t2);
    a1 = arity(t1); a2 = arity(t2);
    if(c1 != c2 || a1 != a2) return <false, bindings>;
    
    kids1 = getChildren(t1); kids2 = getChildren(t2);
    for(int i <- [0 .. a1]){
        if(AType k1 := kids1[i], AType k2 := kids2[i]){
            <res, bindings1> = unify(k1, k2, bindings);
            if(!res) return <res, bindings>;
            bindings += bindings1;
        } else {
            throw "Non AType found while unifying: <kids1[i]>, <kids2[i]>";
        }
    }
    return <true, bindings>;
}

set[Message] validate(REQUIREMENTS extractedRequirements){
          
   overloads = extractedRequirements.overloads;
   facts = extractedRequirements.facts;
   set[Fact] openFacts = extractedRequirements.openFacts;
   openReqs = extractedRequirements.openReqs;
   tvScopes = extractedRequirements.tvScopes;
   
   map[Key, Key] defs = ();
   
   rel[loc, Requirement] triggersRequirement = {};
   rel[loc, Requirement] tvtriggersRequirement = {};
   
   rel[loc, Fact] triggersFact = {};
   rel[loc, Fact] tvtriggersFact = {};
   
   set[Use] unresolvedUses = {};
   set[Requirement] requirementJobs = {};
   
   if(cdebug){
      println("overloads:     <size(overloads)>");
      println("facts:         <size(facts)>");
      println("openFacts:     <size(openFacts)>");
      println("openReqs:      <size(openReqs)>");
      printScopeGraph(extractedRequirements);
   }
   
   set[Message] messages = {};
   iterations = 0;
   
   void printState(){
    println("facts:");
        for(Key fact <- facts){
            println("\t<fact>: <facts[fact]>");
        }
    println("triggersFact:");
        for(<loc k, f> <- triggersFact){
            println("<k> ===\> <f.src>, <f.atype>");
        }
    println("tvtriggersRequirement:");
        for(<loc k, r> <- tvtriggersRequirement){
            println("<k> ===\> <r.name>, <r.src>");
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
            for(atype <- rq.dependsOnTV){
                println("\t  dependsOnTV: <atype>");
            }
            println("\t  preds:");
            for(pred <- rq.preds) println("\t    <pred>");
        }
   }
   
   void addFact(loc l, AType atype){
         if(cdebug)println("addFact: <l>, <atype>, <triggersFact[l]>, <triggersRequirement[l]>");
        
         if(typeof(loc other) := atype){// || tvar(loc other) := atype){
            if(facts[other]?){
               if(cdebug)println("add: facts[<l>] = <facts[other]>");
               facts[l] = facts[other];
            } else {
               fct = openFact({other}, {}, l, atype);
               if(cdebug)println("add: <fct>");
               openFacts += fct;
               triggersFact += <other, fct>;
            }
         } else {
            if(cdebug)println("add: facts[<l>] = <atype>");
            facts[l] = atype;
         }
         
         for(req <- triggersRequirement[l]){
             if(allDependenciesKnown(req.dependsOn, req.dependsOnTV, facts)){
               requirementJobs += req;
               if(cdebug)println("adding requirementJob: <req.name>, <req.src>");
             }
         }
         
         for(fct <- triggersFact[l]){
             if(allDependenciesKnown(fct.dependsOn, fct.dependsOnTV, facts)){
                addFact(fct.src, instantiate(fct.atype, (), facts));
                openFacts -= fct;
             }
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
        for(pred <- preds){
            <ok, bindings1, messages1> = satisfies1(pred, bindings);
            if(cdebug){
               println("*** <pred>");
               println("ok: <ok>, messages: <messages1>");
               if(!isEmpty(bindings1)) println("bindings: <bindings1>");
            }
            
            if(!ok){
               return <false, messages + messages1, ()>;
            }
            req_messages += messages1;
            bindings += bindings1;
            bindings2facts(bindings, req.src);
        }
        
        return <true, req_messages, bindings>;
    }

    // Check the "match" predicate
    tuple[bool ok, map[loc, AType] bindings, set[Message] messages] 
        satisfies1(match(AType pattern, AType subject, ErrorHandler onError), map[loc, AType] bindings){
         if(cdebug)println("match: <pattern>, <subject>, <bindings>");
         pname = getName(pattern);
         pargs = getChildren(pattern);
         
         subject = instantiate(subject, bindings, facts);     
         sname = getName(subject);
         sargs = getChildren(subject);
     
         if(pname != sname || size(pargs) != size(sargs)){
            println("match fail 1");
            return <false, (), {error("<onError.msg>, found <subject>", onError.where)}>;
         }
         bindings = ();
         for(int i <- index(pargs)){
            if(tvar(loc l) := pargs[i] && AType atype := sargs[i]){
                bindings[l] = atype;
            } else {
              throw "Cannot match <pargs[i]> and <sargs[i]>";
            }
         }
         return <true, bindings, {}>;
    }
    
    // Check the "equal" predicate
    tuple[bool ok, map[loc, AType] bindings, set[Message] messages] 
        satisfies1(equal(AType given, AType expected, ErrorHandler onError), map[loc, AType] bindings){
        igiven = instantiate(given, bindings, facts);
        iexpected = instantiate(expected, bindings, facts);
        <ok, bindings1> = unify(igiven, iexpected, bindings);
        return ok ? <true, bindings1, {}> 
                  : <false, bindings, {error("<onError.msg>, expected <AType2String(iexpected)>, found <AType2String(igiven)>", onError.where)}>;
    }
    
    // Check the "fact" predicate
    tuple[bool ok, map[loc, AType] bindings, set[Message] messages] 
        satisfies1(fact(loc l, AType atype), map[loc, AType] bindings){
        addFact(l, instantiate(atype, bindings, facts));
        return <true, (), {}>;
    }
    
 
   for(Fact f <- openFacts){
       if(allDependenciesKnown(f.dependsOn, f.dependsOnTV, facts)){
          addFact(f.src, instantiate(f.atype, (), facts));
          openFacts -= f;
       } else {
           for(dep <- f.dependsOn){
               if(cdebug)println("add: <dep>");
               triggersFact += <dep, f>;
           }
           for(tvdep <- f.dependsOnTV){
               tvtriggersFact += <tvdep, f>;
           }
       }
   } 
    
    for(Define d <- extractedRequirements.defines){
       if(d.defInfo has atype){
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
    
    for(u <- extractedRequirements.uses){
        try {
           println("u = <u>");
           def = lookup(extractedRequirements, u.scope, u);
           println("def = <def>");
           defs[u.occ] = def;
           unresolvedUses += u;
        } catch noKey: {
            messages += error("Undefined variable <u.id>", u.occ);
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
              if(cdebug)println("<fct1>, <deps>, <tvdeps>");
              if(allDependenciesKnown(deps, tvdeps, facts)){ 
                 addFact(u.occ, instantiate(fct1, (), facts));
                 unresolvedUses -= {u};
              }
           }
      }
       
       // eliminate overloads for which argument types are known
       eliminate_overloads:
       for(ovlKey <- extractedRequirements.overloads){
          ovl = extractedRequirements.overloads[ovlKey];
          args = ovl.args;
          if(all(p <- args, facts[p]?)){
              next_alternative:
              for(<argTypes, resType> <- ovl.alternatives){
                  bindings = ();
                  for(int i <- index(argTypes)){
                      iArgType = instantiate(argTypes[i], bindings, facts);
                      iActual = instantiate(facts[args[i]], bindings, facts);
                      <ok, bindings1> = unify(iArgType, iActual, bindings);
                      if(ok){
                        bindings += bindings1;
                      } else {
                        continue next_alternative;
                      }
                  }
                  addFact(ovlKey, resType);
                  overloads = delete(overloads, ovlKey);
                  
                  bindings2facts(bindings, ovl.src);
                  //for(b <- bindings){
                  //   if(cdebug && !facts[b]? && tvScopes[b]?) println("Consider <b>, <bindings[b]>, <isGlobalTypeVar(b)>, <!facts[b]?>, <ovl.src>, <tvScopes[b]>, <ovl.src <= tvScopes[b]>");
                  //   if(isGlobalTypeVar(b) && !facts[b]? && (ovl.src <= tvScopes[b])){
                  //      addFact(b, bindings[b]);
                  //      if(cdebug) println("Adding type var: <b> : <bindings[b]>");
                  //   }
                  //}
                  continue eliminate_overloads;
              }
          }
       }  
       
       // Check open requirements when their predicate can be fully instantiated
       for(oreq <- requirementJobs){
          if(cdebug)println("\nchecking: <oreq.name>, <oreq.src>");
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
                    if(cdebug)println("reqs, adding bound requirement: <instantiate(r, bindings1, facts)>");
                    breq = instantiate(r, bindings1, facts);
                    requirementJobs += { breq };
                }
                for(f <- tfacts){
                    if(cdebug)println("reqs, adding bound fact: <instantiate(f, bindings1, facts)>");
                    fct = instantiate(f, bindings1, facts);
                    addFact(f.src, fct.atype) ;
                }
                
                if(cdebug)println("deleting: <oreq.name>, <oreq.src>");
                  openReqs -= oreq;
                
             } else {
               if(cdebug)println("!ok: <messages1>");
               if(cdebug)println("deleting: <oreq.name>, <oreq.src>");
                  openReqs -= oreq;
             }
          }
      }
   }   
   
   if(size(overloads) > 0){
      for(l <- overloads){
          ovl = overloads[l];
          args = overloads[l].args;
          messages += error("<ovl.onError.msg> <for(int i <- index(args)){><facts[args[i]]? ? AType2String(facts[args[i]]) : "unknown"><i < size(args)-1 ? "," : ""> <}>", ovl.onError.where );
      }
   }
   if(cdebug){
       println("------");
       println("iterations: <iterations>");
       println("overloads:  <size(overloads)>");
       println("facts:      <size(facts)>");
       println("openFacts:  <size(openFacts)>");
       println("openReqs:   <size(openReqs)>");
       
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
   return messages;
}

