@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module typepal::TypePal

import Set; 
import Node;
import Map;
import IO;
import List; 
import ParseTree;
import String;
import Message;
import Exception;

extend typepal::ScopeGraph;
extend typepal::AType;
extend typepal::ExtractFRModel;

syntax ANONYMOUS_OCCURRENCE = "anonymous_occurence";
private loc anonymousOccurrence = ([ANONYMOUS_OCCURRENCE] "anonymous_occurence")@\loc;

bool cdebug = false;

data Exception
    = UnspecifiedMyIsSubType(AType atype1, AType atype2)
    | UnspecifiedMyLUB(AType atype1, AType atype2)
    | UnspecifiedMyATypeMin()
    | UnspecifiedMyATypeMax()
    | UndefinedLUB(AType atype1, AType atype2)
    | TypeUnavailable()
    ;

// ---- defaults for all my* functions

default bool myIsSubType(AType atype1, AType atype2) {
    throw UnspecifiedMyIsSubType(atype1, atype2);
}

default AType myLUB(AType atype1, AType atype2){
    throw UnspecifiedMyLUB(atype1, atype2);
}

default AType myATypeMin(){
    throw UnspecifiedMyATypeMin();
}

default AType myATypeMax(){
    throw UnspecifiedMyATypeMax();
}

default bool myMayOverload(set[Key] defs, map[Key, Define] defines) = false;

// --- Error handling

str fmt(Tree t)  = "`<prettyPrintAType(typeof(t))>`";

void reportError(Tree t, str msg){
    throw error(msg, getLoc(t));
}

set[Message] filterMostPrecise(set[Message] messages){
    res = { msg | msg <- messages, !any(msg2 <- messages, surrounds(msg, msg2)) };
    return res;
}

set[Message] filterMostGlobal(set[Message] messages){
    res = { msg | msg <- messages, !any(msg2 <- messages, surrounds(msg2, msg)) };
    return res;
}
    
bool surrounds (Message msg1, Message msg2){
    // TODO: return msg1.at > msg2.at should also work but does not.
    return msg1.at.offset <= msg2.at.offset && msg1.at.offset + msg1.at.length > msg2.at.offset + msg2.at.length;
}

// Global variables, used by validate and callbacks (define, require, etc.)

// Used outside validate
FRModel extractedFRModel;

map[loc, AType] facts = ();

set[Fact] openFacts = {};
set[Requirement] openReqs = {};
map[loc, AType] bindings = ();
map[loc, set[Requirement]] triggersRequirement = ();
map[loc, set[Fact]] triggersFact = ();

set[Requirement] requirementJobs = {};

set[Key] (FRModel, Use) lookupFun = lookup;

FRModel getFRModel(){
    return extractedFRModel[facts=facts];
}

AType lub(list[AType] atypes) {
    //println("lub: <atypes>");
    minType = myATypeMin();
    lubbedType = (minType | myLUB(it, t) | t <- atypes, isFullyInstantiated(t));
    tvs =  [ t | t <- atypes, tvar(v) := t ];
    other = [t | t <- atypes - tvs, !isFullyInstantiated(t) ];
    lubArgs = (lubbedType == minType ? [] : [lubbedType]) + [ t | t <- atypes, !isFullyInstantiated(t) ];
    if(size(tvs) == 1 && size(other) == 0 && lubbedType == minType){
        return tvs[0];
    }
    if(size(tvs) >= 1 && size(other) == 0 && lubbedType != minType){
        for(tvar(v) <- tvs){
            addFact(v, lubbedType);
            return lubbedType;
        }
    }
    lubArgs = lubbedType + tvs + other;
    switch(size(lubArgs)){
        case 0: return minType;
        case 1: return lubArgs[0];
        default:
                return lazyLub(lubArgs);
    }
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
}

bool allDependenciesKnown(set[loc] deps, bool eager)
    = isEmpty(deps) || (eager ? all(dep <- deps, facts[dep]?)
                             : all(dep <- deps, facts[dep]?, isFullyInstantiated(facts[dep])));

bool isFullyInstantiated(AType atype){
    visit(atype){
        case tvar(name): return facts[name]?;
        case lazyLub(atypes): return isEmpty(atypes) || all(AType tp <- atype, isFullyInstantiated(tp));
        case overloadedAType(overloads): all(<k, tp> <- overloads, isFullyInstantiated(tp));
    }
    return true;
}
// Find a (possibly indirect) binding
AType find(loc src){
    //println("find: <src>");
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

default AType substitute(AType atype){
        return atype;
}

// Recursively instantiate all type variables and useTypes in a type
AType instantiate(AType atype){
  return
      visit(atype){
        case tv: tvar(loc src) => substitute(tv)
        //case AType ut => substitute(ut) when ut has use
        case lazyLub(list[AType] atypes) => lazyLub([substitute(tp) | tp <- atypes])
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
    
    if(atypeList(atypes1) := t1){
       if(atypeList(atypes2) := t2){
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
  
    iatype = instantiate(atype);
    if(cdebug)println("\tadd2: facts[<l>] = <iatype>");
    facts[l] = iatype;
    fireTriggers(l);
    return true;
}

bool addFact(fct:openFact(loc src, set[loc] dependsOn,  AType() getAType)){
    if(cdebug)println("addFact2: <fct>");
    if(allDependenciesKnown(dependsOn, true)){
        try {
            facts[src] = getAType();
            fireTriggers(src);
            return true;
        } catch TypeUnavailable(): /* cannot yet compute type */;
    }
    openFacts += fct;
    for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
    fireTriggers(src);
    return false;
}

bool addFact(fct:openFact(set[loc] defines, set[loc] dependsOn, list[AType()] getATypes)){
    if(cdebug)println("addFact3: <fct>");
    if(allDependenciesKnown(dependsOn, true)){
        try {    
            tp =  (getATypes[0]() | myLUB(it, getAType()) | getAType <- getATypes[1..]);    
            for(def <- defines){ facts[def] = tp;  }
            for(def <- defines) { fireTriggers(def); }
            if(cdebug)println("\taddFact3: lub computed: <tp> for <defines>");
            return true;
        } catch TypeUnavailable(): /* cannot yet compute type */;
    }
    
    // try to partially compute the lub;
    knownTypes = ();
    solve(knownTypes){
        AType currentLub;
        for(int i <- index(getATypes)){
            try {
                knownTypes[i] = getATypes[i]();
                currentLub = currentLub? ? myLUB(currentLub, knownTypes[i]) : knownTypes[i];
            } catch TypeUnavailable(): /*println("unavailable: <i>")*/;
        }
        
        if(currentLub?){
            for(def <- defines){ facts[def] = currentLub;  }
            for(def <- defines) { 
                try fireTriggers(def, protected=false); 
                catch TypeUnavailable():
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
        if(allDependenciesKnown(fct.dependsOn, true)){
           try {
              if(cdebug) println("\tfireTriggers: adding fact: <fct>");
              openFacts -= fct;
              addFact(fct);
           } catch TypeUnavailable(): {
                  /* cannot yet compute type */;
                  if(!protected){
                     throw TypeUnavailable();
                  }
              }
        }
    }
    
    for(req <- triggersRequirement[l] ? {}){
        if(allDependenciesKnown(req.dependsOn, true)){
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
        //println("find(<tree@\loc>) =\> <fct>");
        res = instantiate(fct);
        //println("typeof(<tree@\loc>) =\> <res>");
        return res;
    } catch NoSuchKey(l): {
        //iprintln(facts);
        throw TypeUnavailable();
    }
}

AType typeof(tvar(loc l)){
    try {
        tp = facts[l];
        return tp;
    } catch NoSuchKey(k): {
        throw TypeUnavailable();
    }
}

AType typeof(str id, Key scope, set[IdRole] idRoles){
    try {
        foundDefs = lookupFun(extractedFRModel, use(id, anonymousOccurrence, scope, idRoles));
        if({def} := foundDefs){
           return instantiate(facts[def]);
        } else {
          if(myMayOverload(foundDefs, extractedFRModel.definitions)){
                  return overloadedAType({<d, instantiate(facts[d])> | d <- foundDefs});
          } else {
               throw AmbiguousDefinition(foundDefs);
          }
        }
     } catch NoKey(): {
        println("typeof: <id> in scope <scope> ==\> TypeUnavailable1");
        throw TypeUnavailable();
   }
}

// The "equal" predicate that succeeds or gives error
void equal(AType given, AType expected, ErrorHandler onError){
    if(given != expected){
        throw error("<onError.msg>, expected <fmt(expected)>, found <fmt(given)>", onError.where);
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
        throw error("<onError.msg>", onError.where);
    }
}

// Check the "unify" predicate
bool unify(AType given, AType expected){
    if(tvar(name) := given){
        bindings[name] = expected;
            return true;
    }
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
    if(!myIsSubType(small, large)){
        throw error(onError.msg, onError.where);
    }
}

bool subtype(AType small, AType large){
    extractedFRModel.facts = facts;
    if(isFullyInstantiated(small) && isFullyInstantiated(large)){
       return myIsSubType(small, large);
    } else {
      throw TypeUnavailable();
    }
}

// The "comparable" predicate
void comparable(AType atype1, AType atype2, ErrorHandler onError){
    extractedFRModel.facts = facts;
    if(isFullyInstantiated(atype1) && isFullyInstantiated(atype2)){
        if(!(myIsSubType(atype1, atype2) || myIsSubType(atype2, atype1))){
            throw error(onError.msg, onError.where);
        }
    } else {
        throw TypeUnavailable();
    }
}

default bool comparable(AType atype1, AType atype2){
    extractedFRModel.facts = facts;
    if(isFullyInstantiated(atype1) && isFullyInstantiated(atype2)){
        return myIsSubType(atype1, atype2) || myIsSubType(atype2, atype1);
    } else {
        throw TypeUnavailable();
    }
}

// The "fact" assertion
void fact(Tree t, AType atype){
        addFact(t@\loc, atype);
}

// The "reportError" assertion 
void reportError(loc src, str msg){
    throw Message::error(msg, src);
}

// The "reportWarning" assertion 
void reportWarning(loc src, str msg){
    throw Message::warning(msg, src);
}

/*
 *  validate: validates an extracted FRModel via constraint solving
 *  
 */

FRModel validate(FRModel er,  set[Key] (FRModel, Use) lookupFun = lookup, bool debug = false){
    // Initialize global state
    extractedFRModel = er;
 
    facts = extractedFRModel.facts;
    openFacts = extractedFRModel.openFacts;
    bindings = ();
    openReqs = extractedFRModel.openReqs;
    triggersRequirement = ();
    triggersFact = ();
  
    requirementJobs = {};
    lookupFun = lookupFun;
    
    //luDebug = debug;
    cdebug = debug;
    
    // Initialize local state
    map[Key, set[Key]] defs = ();
    map[loc, Calculator] calculators = extractedFRModel.calculators;
    set[Use] openUses = {};
    set[Message] messages = extractedFRModel.messages;
    iterations = 0;
   
    if(cdebug){
       println("calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
       printFRModel(extractedFRModel);
    }
    
    if(cdebug) println("==== filter double declarations ====");
 
    // Check for illegal overloading in the same scope
    for(<scope, id> <- extractedFRModel.defines<0,1>){
        foundDefines = extractedFRModel.defines[scope, id];
        if(size(foundDefines) > 1){
           ds = {defined | <IdRole idRole, Key defined, DefInfo defInfo> <- foundDefines};
           if(!myMayOverload(ds, extractedFRModel.definitions)){
              messages += {error("Double declaration of `<id>`", defined) | <IdRole idRole, Key defined, DefInfo defInfo>  <- foundDefines};
           }
        }
    }
   
    if(cdebug) println("==== lookup uses ====");
    
    // Check that all uses have a definition and that all overloading is allowed
    
    for(u <- extractedFRModel.uses){
        try {
           foundDefs = lookupFun(extractedFRModel, u);
           //println("<u.id> at <u.occ> =\> <foundDefs>");
           if(size(foundDefs) == 1 || myMayOverload(foundDefs, extractedFRModel.definitions)){
              defs[u.occ] = foundDefs;
              openUses += u;
            } else {
                messages += {error("Double declaration", d) | d <- foundDefs} + error("Undefined `<getId(u)>` due to double declaration", u.occ);
            }
        }
        catch NoKey():
            messages += error("Undefined `<getId(u)>`", u.occ);
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
        if(allDependenciesKnown(oreq.dependsOn, oreq.eager)){
           requirementJobs += oreq;
        }
    }
  
           
    solve(facts, openReqs, openFacts, openUses, requirementJobs){       
       if(cdebug){
          println("======================== iteration <iterations>");
          printState();
       }
       
       for(Fact f <- openFacts){
           if(addFact(f)){
                openFacts -= f;
           }
       }
       
       for(u <- openUses){
           foundDefs = defs[u.occ];
           if (cdebug) println("Consider unresolved use: <u>, foundDefs=<foundDefs>");
           if({def} := foundDefs){  // unique definition found
               if(facts[def]?){  // has type of def become available?
                  fct1 = facts[def];
                  addFact(u.occ, instantiate(fct1));
                  openUses -= u;
                  if (cdebug) println("Resolved use: <u>");
               } else {
                  if(cdebug) println("not yet known: <def>");
               }
            } else {                // Multiple definitions found
                if(all(d <- foundDefs, facts[d]?)){ 
                   addFact(u.occ, overloadedAType({<d, instantiate(facts[d])> | d <- foundDefs}));
                   openUses -= u;
                }
            }
       }
      
       // eliminate calculators for which argument types are known
       for(calcKey <- calculators){
          calc = calculators[calcKey];
          if(allDependenciesKnown(calc.dependsOn, calc.eager)){
              try {
                t = calc.calculator();
                addFact(calcKey, t);
                bindings2facts(bindings, calc.src); 
              } catch TypeUnavailable(): {
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
          if(allDependenciesKnown(oreq.dependsOn, oreq.eager)){ 
             if(cdebug)println("\tchecking `<oreq.name>`: dependencies are available");  
             try {       
                 <ok, messages1, bindings1> = satisfies(oreq); 
                 if(cdebug)println("\tok=<ok>, <messages1>, <bindings1>");
                 messages += messages1;
                 if(ok){
                    if(cdebug)println("\tchecking `<oreq.name>`: bindings: <bindings1>");
                    for(tv <- domain(bindings1), f <- triggersFact[tv] ? {}){
                        if(allDependenciesKnown(f.dependsOn, true)){
                            try {
                                if(cdebug)println("\tchecking `<oreq.name>`: adding bound fact: <f>");
                                addFact(f.src, f.getAType());
                                openFacts -= {f};
                            } catch TypeUnavailable(): /* cannot yet compute type */;
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
             } catch TypeUnavailable():
                ;//println("checking `<oreq.name>`: dependencies not yet available");
          } else {
            ;//println("\tchecking `<oreq.name>`: dependencies not yet available");
          }
         }
       } 
    
       for (u <- openUses) {
          foundDefs = defs[u.occ];
          for(def <- foundDefs){
              if (facts[def]?) {
              //  deps = extractTypeDependencies(facts[def]);
              //  if (!allDependenciesKnown(deps, true)) {
              //    messages += { error("Unresolved dependencies for `<u.id>`: <deps>", u.occ) };
              //  }
              //  else {
              //    messages += { error("Undefined `<u.id>` for unknown reason; points to <def> with type <facts[def]> and dependencies <deps>", u.occ)};
              //  }
              //} else {   
                messages += { error("Unresolved type for `<u.id>`", u.occ)};
              }
          }
       }
    
       for(l <- calculators){
           calc = calculators[l];
           deps = toList(calculators[l].dependsOn);
           messages += error("Type of <calc.name> could not be computed for <for(int i <- index(deps)){><facts[deps[i]]? ? "`<prettyPrintAType(facts[deps[i]])>`" : "`unknown type`"><i < size(deps)-1 ? "," : ""> <}>", calc.src );
       }
  
       messages += { error("Invalid <req.name>; type of one or more subparts could not be inferred", req.src) | req <- openReqs};
   
       if(cdebug){
           println("------");
           println("iterations: <iterations>; calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
           printState();
           println("calculators:");
           for(c <- calculators){
                calc = calculators[c];
                println("\t<calc.name> at <calc.src>:");
                for(atype <- calc.dependsOn){
                    println("\t  dependsOn: <atype>");
                }
           }
           
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
       return myPostValidation(er);
}

rel[loc, loc] getUseDef(FRModel frm){
    res = {};
    for(Use u <- frm.uses){
        try {
           foundDefs =  lookup(frm, u);
           res += { <u.occ, def> | def <- foundDefs };
        } catch NoKey(): {
            ;// ignore it
        } catch AmbiguousDefinition(_):{
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
