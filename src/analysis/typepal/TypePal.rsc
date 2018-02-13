@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::TypePal

import Set; 
import Node;
import Map;
import IO;
import List; 
import ParseTree;
import String;
import Message;
import Exception;

import util::Benchmark;

extend analysis::typepal::ScopeGraph;
extend analysis::typepal::AType;
extend analysis::typepal::ExtractTModel;
extend analysis::typepal::TypePalConfig;

syntax ANONYMOUS_OCCURRENCE = "anonymous_occurence";
private loc anonymousOccurrence = ([ANONYMOUS_OCCURRENCE] "anonymous_occurence")@\loc;

// Configuration 

bool cdebug = false;

bool(AType,AType) isSubTypeFun = defaultIsSubType;

AType(AType,AType) getLubFun = defaultGetLub;

AType() getMinATypeFun = defaultGetMinAType;

AType theMinAType = atypeList([]);
AType theMaxAType = atypeList([]);

AType() getMaxATypeFun = defaultGetMaxAType;

bool defaultMayOverload(set[Key] defs, map[Key, Define] defines) = false;

bool (set[Key] defs, map[Key, Define] defines) mayOverloadFun = defaultMayOverload;

void configTypePal(TypePalConfig tc){
    analysis::typepal::ScopeGraph::configScopeGraph(tc);
    
    isSubTypeFun = tc.isSubType;
    getLubFun = tc.getLub;
    mayOverloadFun = tc.mayOverload;
    lookupFun = tc.lookup;
    
    getLubDefined = false;
    try {
        getLubFun(atypeList([]), atypeList([]));
        getLubDefined = true;
    }  catch TypePalUsage(_): {
        getLubDefined = false;
    }
    
    try {
        theMinAType = tc.getMinAType();
    } catch TypePalUsage(_):{
        if(getLubDefined) throw TypePalUsage("`getMinAType` should be defined when `getLub` is used");
    }
    
    try {
        theMaxAType = tc.getMaxAType();
    } catch TypePalUsage(_):{
        if(getLubDefined) throw TypePalUsage("`getMaxAType` should be defined when `getLub` is used");
    }
    
    getMinATypeFun = tc.getMinAType;
    getMaxATypeFun = tc.getMaxAType;
   
}

// --- Error handling

Message error(Tree t, str msg) = error(msg, getLoc(t));

Message warning(Tree t, str msg) = warning(msg, getLoc(t));

Message info(Tree t, str msg) = info(msg, getLoc(t));

bool reportError(Tree t, str msg){
    throw checkFailed({error(msg, getLoc(t))});
}

bool reportError(loc l, str msg){
    throw checkFailed({error(msg, l)});
}

bool reportWarning(Tree t, str msg){
    messages += {warning(msg, getLoc(t))};
    return true;
}

bool reportInfo(Tree t, str msg){
    messages += {info(msg, getLoc(t))};
    return true;
}

bool reportErrors(set[Message] msgs){
    throw checkFailed(msgs);
}

// Is inner location textually contained in outer location?
bool containedIn(loc inner, loc outer){
    return inner.path == outer.path && inner.offset >= outer.offset && inner.offset + inner.length <= outer.offset + outer.length;
}

list[Message] sortMostPrecise(list[Message] messages)
    = sort(messages, bool (Message a, Message b) {
        loc al = a.at;
        loc bl = b.at;
        return (al.length / 10) < (bl.length / 10) || al.top < bl.top;
    });
 
bool alreadyReported(set[Message] messages, loc src) 
    = !isEmpty(messages) && any(msg <- messages, containedIn(msg.at, src));

// ---- Some formatting utilities

str fmt(Tree t)  = "`<prettyPrintAType(getType(t))>`";

str intercalateAnd(list[str] strs){
    switch(size(strs)){
      case 0: return "";
      case 1: return strs[0];
      default: 
              return intercalate(", ", strs[0..-1]) + " and " + strs[-1];
      };
}

str intercalateOr(list[str] strs){
    switch(size(strs)){
      case 0: return "";
      case 1: return strs[0];
      default: 
              return intercalate(", ", strs[0..-1]) + " or " + strs[-1];
      };
}

// Global variables, used by validate and callbacks (define, require, etc.)

// Used outside validate
TModel extractedTModel;

map[loc, AType] facts = ();

set[Fact] openFacts = {};
set[Requirement] openReqs = {};
map[loc, AType] bindings = ();
map[loc, set[Requirement]] triggersRequirement = ();
map[loc, set[Fact]] triggersFact = ();

set[Requirement] requirementJobs = {};

set[Message] messages = {};

public set[Key] (TModel, Use) lookupFun = lookup;

TModel getTModel(){
    return extractedTModel[facts=facts];
}

void clearBindings() { 
    if(!isEmpty(bindings)) 
        println("clearBindings: <bindings>");
    bindings = (); 
}

void keepBindings(loc tvScope) { 
    if(!isEmpty(bindings)){
        res = (b : bindings[b] | b <- bindings, containedIn(b, tvScope));
        //println("keepBindings, <tvScope>: <bindings> ==\> <res>");
       bindings = res;
    }
}

AType simplifyLub(list[AType] atypes) {
    //println("simplifyLub: <atypes>");
    lubbedType = theMinAType;
    other = [];
    for(t <- atypes){
        if(isFullyInstantiated(t)){
            lubbedType = getLubFun(lubbedType, t);
        } else {
            other += t; 
        }
    }
   
    if(lubbedType != theMinAType){
        bindings1 = bindings;
        bindings = ();
        other = [t | t <- other, !unify(lubbedType, t)];
        for(b <- bindings){
            println("add <b>, <bindings[b]>");
            addFact(b, bindings[b]);
        }
        bindings = bindings1;
    }
   res = lubbedType;
    switch(size(other)){
        case 0:  res = lubbedType;
        case 1:  res = lubbedType == theMinAType ? other[0] : lazyLub(lubbedType + other);
        default: res = lubbedType == theMinAType ? lazyLub(other) : lazyLub(lubbedType + other);
    }
    //println("simplifyLub: <atypes> ==\> <res>");
    return res;
}

void printState(){
    println("Derived facts:");
        for(Key fact <- facts){
            println("\t<fact>: <facts[fact]>");
        }
    if(size(openFacts) > 0){
        println("Unresolved facts:");
        for(Fact fact <- openFacts){
            if(fact has src){
                println("\t<fact.src>"); 
            } else {
                println("\t<fact.srcs>");
            }
            if(fact has uninstantiated){
                println("\t  dependsOn: <fact.uninstantiated>");
            } else if(isEmpty(fact.dependsOn)){
                println("\t  dependsOn: nothing");
            } else {
                for(dep <- fact.dependsOn){
                    println("\t  dependsOn: <dep><facts[dep]? ? "" : " ** unavailable **">");
                }
            }
            println("\t<fact>");
        }
    }
    if(size(openReqs) > 0){
        println("Unresolved requirements:");
        for(rq <- openReqs){
            println("\t<rq.rname> at <rq.src>:");
            for(atype <- rq.dependsOn){
                println("\t  dependsOn: <atype><facts[atype]? ? "" : " ** unavailable **">");
            }
        }
    }
}

bool allDependenciesKnown(set[loc] deps, bool eager)
    = isEmpty(deps) || (eager ? all(dep <- deps, facts[dep]?)
                              : all(dep <- deps, facts[dep]?, isFullyInstantiated(facts[dep])));

bool allDependenciesKnown(list[loc] deps, bool eager)
    = isEmpty(deps) || (eager ? all(dep <- deps, facts[dep]?)
                              : all(dep <- deps, facts[dep]?, isFullyInstantiated(facts[dep])));


bool isFullyInstantiated(AType atype){
    visit(atype){
        case tvar(loc tname): if(!facts[tname]? || tvar(tname) := facts[tname]) return false; // return facts[tname]? && isFullyInstantiated(facts[tname]);
        case lazyLub(list[AType] atypes): if(!(isEmpty(atypes) || all(AType tp <- atype, isFullyInstantiated(tp)))) return false;
        case overloadedAType(rel[Key, IdRole, AType] overloads): all(<k, idr, tp> <- overloads, isFullyInstantiated(tp));
    }
    return true;
}
// Find a (possibly indirectly defined) type for src
AType findType(loc src){
    //println("findType: <src>");
    if(bindings[src]?){
        v = bindings[src];
        if(tvar(loc src1) := v && src1 != src && (bindings[src1]? || facts[src1]?)) return findType(src1);
        //println("findType==\> <v>");
        return v;
    }
    if(facts[src]?){
        v = facts[src];
        if(tvar(loc src1) := v && src1 != src && (bindings[src1]? || facts[src1]?)) return findType(src1);
        //println("findType==\> <v>");
        return v;
    }
   throw NoSuchKey(src);
}

// Substitute a type variable first using bindings, then facts; return as is when there is no binding
AType substitute(tv: tvar(loc src)){
    if(bindings[src]?) { b = bindings[src]; return b == tv ? tv : substitute(b); }
    if(facts[src]?) { b = facts[src]; return b == tv ? tv : substitute(b); }
    return tv;
}

default AType substitute(AType atype){
        return atype;
}

// Recursively instantiate all type variables and lazyLubs in a type
AType instantiate(AType atype){
  return
      visit(atype){
        case tv: tvar(loc src) => substitute(tv)
        case lazyLub(list[AType] atypes) : {
            sbs = [substitute(tp) | tp <- atypes];
            insert simplifyLub(sbs);
            }
      };
}

// Unification of two types, for now, without checks on variables
tuple[bool, map[loc, AType]] unify(AType t1, AType t2, map[loc, AType] bindings){
    //println("unify: <t1>, <t2>");
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
    
    // TODO:introducing lazyLub in unify is an interesting idea but is it correct?
    if(lazyLub(lubbables1) := t1 && lazyLub(lubbables2) !:= t2){
        for(lb <- toSet(lubbables1)){
            if(tvar(loc tv) := lb){
               bindings += (tv : t2) + bindings;
            }
        }
        return <true, bindings>;
    }
    
    if(lazyLub(lubbables1) !:= t1 && lazyLub(lubbables2) := t2){
        for(lb <- toSet(lubbables2)){
            if(tvar(loc tv) := lb){
               bindings += (tv : t1) + bindings;
            }
        }
        return <true, bindings>;
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
            if( kids1[i] != kids2[i] ){
                return <false, bindings>;
            }
        }
    }
    return <true, bindings>;
}
    
bool addFact(<Key scope, str id, IdRole idRole, Key defined, noDefInfo()>) 
    = true;
 
bool addFact(<Key scope, str id, IdRole idRole, Key defined, defType(AType atype)>) 
    = isFullyInstantiated(atype) ? addFact(defined, atype) : addFact(openFact(defined, atype));
    
bool addFact(<Key scope, str id, IdRole idRole, Key defined, defType(set[Key] dependsOn, AType() getAType)>) 
    = addFact(openFact(defined, dependsOn, getAType));

bool addFact(<Key scope, str id, IdRole idRole, Key defined, defLub(set[Key] dependsOn, set[Key] defines, list[AType()] getATypes)>) 
    = addFact(openFact(defines, dependsOn, getATypes));

default bool addFact(Define d) {  throw TypePalInternalError("Cannot handle <d>"); }


bool addFact(loc l, AType atype){
    //println("addFact: <l>, <atype>");
    iatype = instantiate(atype);
    if(!mayReplace(l, iatype)){ println("####5 <l>: <facts[l]> not replaced by <iatype>"); return false; }
    facts[l] = iatype;
    if(cdebug)println(" fact <l> ==\> <iatype>");
    if(tvar(tvloc) := iatype){
        triggersFact[tvloc] = (triggersFact[tvloc] ? {}) + {openFact(l, iatype)};
    } else {
        fireTriggers(l);
    }
    return true;
}

set[loc] getDependencies(AType atype){
    deps = {};
    visit(atype){
        case tv: tvar(loc src) : deps += src;
    };
    return deps;
}

// If we already have type info for a location, may we replace that with newer info?
bool mayReplace(loc src, AType newType){
    if(!facts[src]?) return true;
    oldType = facts[src];
    if(tvar(x) := oldType) return true;
    if(tvar(x) := newType) return true;
    try {
        return isSubTypeFun(oldType, newType);
    } catch TypePalUsage(s): return false;
}

bool addFact(fct:openFact(loc src, AType uninstantiated)){
    if(!(uninstantiated is lazyLub)){
        try {
            iatype = getType(uninstantiated); //instantiate(uninstantiated); //getType(uninstantiated);
            if(!mayReplace(src, iatype)){ println("####1 <src>: <facts[src]> not replaced by <iatype>"); return true; }
            facts[src] = iatype;
            dependsOn = getDependencies(iatype);
            if(allDependenciesKnown(dependsOn, false) && src notin dependsOn) fireTriggers(src);
            return true;
        } catch TypeUnavailable(): /* cannot yet compute type */;
    }
    openFacts += fct;
    dependsOn = getDependencies(uninstantiated) - src; // <===
    for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
    fireTriggers(src);
    return false;
}

bool addFact(fct:openFact(loc src, set[loc] dependsOn,  AType() getAType)){
    //if(cdebug)println("addFact2: <fct>");
    if(allDependenciesKnown(dependsOn, true)){
        try {
            iatype = getAType();
            if(!mayReplace(src, iatype)){ println("####2 <src>: <facts[src]> =!=\> <iatype>"); return true; }
            facts[src] = iatype;
            if(cdebug)println(" fact <src> ==\> <facts[src]>");
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
    if(cdebug)println("addFact LUB: <fct>");
    
    if(allDependenciesKnown(dependsOn, true)){
        try {    
            computedTypes = [instantiate(getAType()) | getAType <- getATypes];
            if(any(tp <- computedTypes, tvar(l) := tp)) throw TypeUnavailable();
            tp = simplifyLub(computedTypes);
            //tp =  (getATypes[0]() | getLubFun(it, getAType()) | getAType <- getATypes[1..]);    
            for(def <- defines){ 
               if(!mayReplace(def, tp)){
                  println("####3 <def>: <facts[def]> not replaced by <tp>");
              } else {
                 facts[def] = tp;  
                 if(cdebug)println(" fact3 <def> ==\> <tp>");
              }
            }
            for(def <- defines) { fireTriggers(def); }
            if(cdebug)println("\taddFact3: lub computed: <tp> for <defines>");
            return true;
        } catch TypeUnavailable(): /* cannot yet compute type */;
    }
    
    // try to partially compute the lub;
    //if(cdebug) println("try to partially compute the lub");
    knownTypes = ();
    solve(knownTypes){
        AType currentLub;
        for(int i <- index(getATypes)){
            try {
                tp = getATypes[i]();
                if(isFullyInstantiated(tp)){
                    currentLub = currentLub? ? getLubFun(currentLub, tp) : tp;
                    knownTypes[i] = tp;
                }
            } catch TypeUnavailable(): /*println("unavailable: <i>")*/;
        }
        
        if(currentLub?){
            for(def <- defines){ 
                if(!mayReplace(def, currentLub)){
                    println("####4 <def>: <facts[def]> not replaced by <currentLub>");
                } else {
                    facts[def] = currentLub; 
                }
            }
            for(def <- defines) { 
                try fireTriggers(def, protected=false); 
                catch TypeUnavailable():
                    ;//facts = delete(facts, def);
            }
        }
    }
    if(size(knownTypes) == size(getATypes))
        return true;
    
    if(cdebug) println("last resort");
    // last resort
    openFacts += fct;
    //if(cdebug)println("\taddFact: adding dependencies: <dependsOn>");
    for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
    //for(d <- defines) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
    for(def <- defines) fireTriggers(def);
    return false;
}

default void addFact(Fact fct) {
    throw TypePalInternalError("Cannot handle <fct>");
}

void fireTriggers(loc l, bool protected=true){
    //if(cdebug) println("\tfireTriggers: <l>");
    
    for(fct <- triggersFact[l] ? {}){        
        if(fct has uninstantiated || allDependenciesKnown(fct.dependsOn, true)){
           try {
              if(cdebug) println("\tfireTriggers: adding fact: <fct>");
              openFacts -= fct;
              if(fct has src){
                 if(!facts[fct.src]? || tvar(x) := facts[fct.src]) addFact(fct);
              } else {
                 addFact(fct);
              }
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
           //if(cdebug)println("\tfireTriggers: adding requirementJob: <req.rname>, <req.src>");
        }
    }
}

// The binding of a type variable that occurs inside the scope of that type variable can be turned into a fact
void bindings2facts(map[loc, AType] bindings, loc occ){
   
    for(b <- bindings){
        if(cdebug) println("bindings2facts: <b>, <facts[b]? ? facts[b] : "**undefined**">");
        if(!facts[b]? || tvar(x) := facts[b]){
           addFact(b, bindings[b]);
           if(cdebug) println("bindings2facts, added: <b> : <bindings[b]>");
        } else {
           oldTp = facts[b];
           if(lazyLub(list[AType] atypes) := oldTp){
              addFact(b, bindings[b]);
              if(cdebug){ println("bindings2facts, added: <b> : <bindings[b]>"); }
           } else
           if(cdebug) println("bindings2facts, not added: <b>");
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
    } catch checkFailed(set[Message] msgs):
        return <false, msgs, bindings>;
}

// The "run-time" functions that can be called from requirements and calculators

@doc{
.Synopsis
Get type of a tree as inferred by specified type checker

.Description
xxx
}    
AType getType(Tree tree) {
    try {
        return  instantiate(findType(tree@\loc));
    } catch NoSuchKey(l): {
        //println("getType: <tree@\loc> unavailable");
        throw TypeUnavailable();
    }
}

AType getType(tvar(loc l)){
    try {
        return facts[l];
    } catch NoSuchKey(k): {
        throw TypeUnavailable();
    }
}

default AType getType(AType atype){
    try {
        return instantiate(atype);
    } catch NoSuchKey(k): {
        throw TypeUnavailable();
    }
}

AType getType(loc l){
    try {
        return facts[l];
    } catch NoSuchKey(k): {
        throw TypeUnavailable();
    }
}

@memo
AType getType(str id, Key scope, set[IdRole] idRoles){
    try {
        foundDefs = lookupFun(extractedTModel, use(id, anonymousOccurrence, scope, idRoles));
        if({def} := foundDefs){
           return instantiate(facts[def]);
        } else {
          if(mayOverloadFun(foundDefs, extractedTModel.definitions)){
                  return overloadedAType({<d, idRole, instantiate(facts[d])> | d <- foundDefs, idRole := extractedTModel.definitions[d].idRole, idRole in idRoles});
          } else {
               //throw AmbiguousDefinition(foundDefs);
                reportErrors({error("Double declaration of <fmt(id)>", d) | d <- foundDefs} /*+ error("Undefined `<id>` due to double declaration", u.occ) */);
          }
        }
     } catch NoSuchKey(k): {
            throw TypeUnavailable();
            }
       catch NoKey(): {
            //println("getType: <id> in scope <scope> as <idRoles> ==\> TypeUnavailable1");
            throw TypeUnavailable();
       }
}

Define getDefinition(Tree tree){
    try {
        println("getDefinition: <tree>,  <getLoc(tree)>");
        return extractedTModel.definitions[getLoc(tree)];
     } catch NoSuchKey(k):
            throw TypeUnavailable();
       catch NoKey(): {
            throw TypeUnavailable();
       }
}

set[Define] getDefinitions(str id, Key scope, set[IdRole] idRoles){
    try {
        foundDefs = lookupFun(extractedTModel, use(id, anonymousOccurrence, scope, idRoles));
        if({def} := foundDefs){
           return {extractedTModel.definitions[def]};
        } else {
          if(mayOverloadFun(foundDefs, extractedTModel.definitions)){
            return {extractedTModel.definitions[def] | def <- foundDefs};
          } else {
               throw AmbiguousDefinition(foundDefs);
          }
        }
     } catch NoSuchKey(k):
            throw TypeUnavailable();
       catch NoKey(): {
            //println("getDefinitions: <id> in scope <scope> ==\> TypeUnavailable2");
            throw TypeUnavailable();
       }
}

set[Define] getDefinitions(Tree tree, set[IdRole] idRoles)
    = getDefinitions(getLoc(tree), idRoles);

set[Define] getDefinitions(Key scope, set[IdRole] idRoles)
    = {<scope, id, idRole, defined, defInfo> | <str id, IdRole idRole, Key defined, DefInfo defInfo> <- extractedTModel.defines[scope], idRole in idRoles };


// Check the "equal" predicate
bool equal(AType given, AType expected){
    return unsetRec(given) == unsetRec(expected);
}

// Check the "unify" predicate
bool unify(AType given, AType expected){
    if(tvar(tname) := given){
        bindings[tname] = expected;
            return true;
    }
    if(tvar(tname) := expected){
        bindings[tname] = given;
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

bool subtype(AType small, AType large){
    extractedTModel.facts = facts;
    if(isFullyInstantiated(small) && isFullyInstantiated(large)){
       r = isSubTypeFun(small, large);
       //println("subtype: <small>, <large> ==\> <r>");
       return r;
    } else {
      throw TypeUnavailable();
    }
}

default bool comparable(AType atype1, AType atype2){
    extractedTModel.facts = facts;
    if(isFullyInstantiated(atype1) && isFullyInstantiated(atype2)){
        return isSubTypeFun(atype1, atype2) || isSubTypeFun(atype2, atype1);
    } else {
        throw TypeUnavailable();
    }
}

// lub

AType lub(AType t1, AType t2) = simplifyLub([t1, t2]);
AType lub(list[AType] atypes) = simplifyLub(atypes);

// The "fact" assertion
void fact(Tree t, AType atype){
        addFact(t@\loc, atype);
}

void fact(loc src, AType atype){
        addFact(src, atype);
}

//// Report an error: WARNING throws an exception and aborts normal control flow 
//void reportError(loc src, str msg){
//    throw checkFailed({Message::error(msg, src)});
//}

//// Report a warning: WARNING throws an exception and aborts normal control flow 
//void reportWarning(loc src, str msg){
//    throw {Message::warning(msg, src)}; // TODO FIXME
//}

/*
 *  validate: validates an extracted TModel via constraint solving
 *  
 */

TModel validate(TModel tmodel, bool debug = false){

    configTypePal(tmodel.config);
    
    // Initialize global state
    extractedTModel = tmodel;
      
    facts = extractedTModel.facts;
    openFacts = extractedTModel.openFacts;
    bindings = ();
    openReqs = extractedTModel.openReqs;
    messages = {*extractedTModel.messages};
    triggersRequirement = ();
    triggersFact = ();
  
    requirementJobs = {};
    //lookupFun = lookupFun;
    
    //luDebug = debug;
    cdebug = debug;
    
    // Initialize local state
    map[Key, set[Key]] definedBy = ();
    map[loc, Calculator] calculators = extractedTModel.calculators;
    set[Use] openUses = {};
    
    int iterations = 0;
   
    if(cdebug){
       println("calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
       printTModel(extractedTModel);
    }
    
    if(cdebug) println("..... filter double declarations");
 
    // Check for illegal overloading in the same scope
    for(<scope, id> <- extractedTModel.defines<0,1>){
        foundDefines = extractedTModel.defines[scope, id];
        if(size(foundDefines) > 1){
           ds = {defined | <IdRole idRole, Key defined, DefInfo defInfo> <- foundDefines};
           if(!mayOverloadFun(ds, extractedTModel.definitions)){
                messages += {error("Double declaration of `<id>`", defined) | <IdRole idRole, Key defined, DefInfo defInfo>  <- foundDefines};
           }
        }
    }
   
    if(cdebug) println("..... lookup uses");
    
    // Check that all uses have a definition and that all overloading is allowed
    for(Use u <- extractedTModel.uses){
        try {
           foundDefs = lookupFun(extractedTModel, u);
           
           if(isEmpty(foundDefs)){
              roles = size(u.idRoles) > 3 ? "name" : intercalateOr([replaceAll(getName(idRole), "Id", "") | idRole <-u.idRoles]);
              messages += error("Undefined <roles> `<getId(u)>`", u.occ);
           } else 
           if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, extractedTModel.definitions)){
              definedBy[u.occ] = foundDefs;
              openUses += u;
              if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <foundDefs>");
            } else {
                messages += {error("Double declaration", d) | d <- foundDefs} + error("Undefined `<getId(u)>` due to double declaration", u.occ);
                if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** double declaration **");
            }
        }
        catch NoKey(): {
            roles = size(u.idRoles) > 5 ? "" : intercalateOr([replaceAll(getName(idRole), "Id", "") | idRole <-u.idRoles]);
            messages += error("Undefined <roles> `<getId(u)>`", u.occ);
            if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** undefined **");
        }
    }
    
    if(cdebug) println("..... handle defines");

    for(Define d <- extractedTModel.defines){
        //if(d.id in {/*"Grammar","Exception",*/"CharClass","StringConstant"}) println("Defined: <d>");
        try addFact(d);
        catch checkFailed(set[Message] msgs):
            messages += msgs;
    }
 
    if(cdebug) println("..... handle open facts");
    for(Fact f <- openFacts){
        try {
            if(addFact(f)){
                openFacts -= f;
            }
        } catch checkFailed(set[Message] msgs): 
            messages += msgs;
    } 
    
    if(cdebug) println("..... handle open requirements");
    for(Requirement oreq <- openReqs){
       for(dep <- oreq.dependsOn){
           triggersRequirement[dep] = (triggersRequirement[dep] ? {}) + {oreq};
           //println("add trigger <dep> ==\> <oreq.rname>");
       }
    }

    for(Requirement oreq <- openReqs){
        if(allDependenciesKnown(oreq.dependsOn, oreq.eager)){
           requirementJobs += oreq;
        }
    }
  
    /****************** main solve loop *********************************/
    
    if(cdebug) println("..... start solving");
    int nfacts = size(facts);
    int nopenReqs = size(openReqs);
    int nopenFacts = size(openFacts);
    int nopenUses = size(openUses);
    int nrequirementJobs = size(requirementJobs);
    int ncalculators = size(calculators);
    
    
    solve(nfacts, nopenReqs, nopenFacts, nopenUses, nrequirementJobs, ncalculators){ 
        
        iterations += 1;
        
        println("iteration: <iterations>; calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
        
       // ---- openUses
       
       openUsesToBeRemoved = {};
       
       handleOpenUses:
       for(Use u <- sort(openUses, bool(Use a, Use b){ return a.occ.offset < b.occ.offset; })){
       //for(Use u <- openUses){
           foundDefs = definedBy[u.occ];
           if (cdebug) println("Consider unresolved use: <u>, foundDefs=<foundDefs>");
           
           try {
               if({def} := foundDefs){  // unique definition found for use u
                   if(facts[def]?){     // has type of its definition become available?
                      addFact(u.occ, facts[def]);
                      openUsesToBeRemoved += u;
                      if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ]>");
                   } else {
                      if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ] ? "** unavailable **">");
                   }
                } else {                // Multiple definitions found
                    foundDefs1 = {d | d <- foundDefs, extractedTModel.definitions[d].idRole in u.idRoles}; 
                    for(dkey <- foundDefs1){
                        try  addFact(extractedTModel.definitions[dkey]);
                         catch TypeUnavailable():
                            continue handleOpenUses;
                    }
                    if(all(d <- foundDefs1, facts[d]?)){ 
                       addFact(u.occ, overloadedAType({<d, extractedTModel.definitions[d].idRole, instantiate(facts[d])> | d <- foundDefs1}));
                       openUsesToBeRemoved += u;
                       if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ]>");
                    }
                }
            } catch checkFailed(set[Message] msgs):
                messages += msgs;
       }
       
       openUses -= openUsesToBeRemoved;
      
       // ---- calculators
      
       calculatorsToBeRemoved = {};
       for(Key calcKey <- sort(domain(calculators), bool(Key a, Key b){ return a.offset < b.offset; })){
       //for(Key calcKey <- calculators){
          calc = calculators[calcKey];
          if(cdebug) println("?calc [<calc.cname>] at <calc.src>"); 
          if(allDependenciesKnown(calc.dependsOn, calc.eager)){
              try {
                t = calc.calculator();
                addFact(calcKey, t);
                bindings2facts(bindings, calc.src);
                if(cdebug) println("+calc [<calc.cname>] at <calc.src> ==\> <t>"); 
              } catch TypeUnavailable(): {
                continue;
              } catch checkFailed(set[Message] msgs): {
                messages += msgs;
                if(cdebug) println("-calc [<calc.cname>] at <calc.src> ==\> <msgs>");
              }
              calculatorsToBeRemoved += calcKey;
          }
       }
       calculators = domainX(calculators, calculatorsToBeRemoved);
       
       // ---- open requirements
       
       openFactsToBeRemoved = {};
       openReqsToBeRemoved = {};
       requirementJobsToBeRemoved = {};
       for(Requirement oreq <- sort(requirementJobs, bool(Requirement a, Requirement b){ return a.src.offset < b.src.offset; })){
          if(allDependenciesKnown(oreq.dependsOn, oreq.eager)){  
             try {       
                 <ok, messages1, bindings1> = satisfies(oreq); 
                 messages += messages1;
                 if(ok){
                    for(tv <- domain(bindings1), f <- triggersFact[tv] ? {}){
                        if(f has uninstantiated){
                         try {
                                if(addFact(f.src, instantiate(f.uninstantiated)))
                                   openFactsToBeRemoved += f;
                            } catch TypeUnavailable(): /* cannot yet compute type */;
                        }
                        else if(allDependenciesKnown(f.dependsOn, true)){
                            try {
                                if(addFact(f.src, f.getAType()))
                                   openFactsToBeRemoved += f;
                            } catch TypeUnavailable(): /* cannot yet compute type */;
                        }
                    }
                 }
                 if(cdebug)println("<ok ? "+" : "-">requ [<oreq.rname>] at <oreq.src>");
                 openReqsToBeRemoved += oreq;
                 requirementJobsToBeRemoved += oreq;
             } catch TypeUnavailable():/* cannot yet compute type */;
           }
         }
         
         openFacts -= openFactsToBeRemoved;
         openReqs -= openReqsToBeRemoved;
         requirementJobs -= requirementJobsToBeRemoved;
         
         // ---- open facts
         
         if(cdebug) println("..... handle openFacts");
    
         openFactsToBeRemoved = {};
         for(Fact fct <- sort(openFacts, 
                              bool(Fact a, Fact b){
                                asrc = a has src ? a.src.offset : sort(a.srcs)[0].offset;
                                bsrc = b has src ? b.src.offset : sort(b.srcs)[0].offset;
                                return asrc < bsrc; })){
         //for(Fact fct <- openFacts){
             try {
             	if(addFact(fct))
                    openFactsToBeRemoved += fct;
             } catch checkFailed(set[Message] msgs):
            		messages += msgs;
         }
         openFacts -= openFactsToBeRemoved;
         
        nfacts = size(facts);
        nopenReqs = size(openReqs);
        nopenFacts = size(openFacts);
        nopenUses = size(openUses);
        nrequirementJobs = size(requirementJobs);
        ncalculators = size(calculators);
       }
       
       /****************** end of main solve loop *****************************/
       
       if(cdebug) println("..... solving complete");
       
       //iprintln(facts, lineLimit=10000);
    
       for (Use u <- openUses) {
          foundDefs = definedBy[u.occ];
          for(def <- foundDefs){
              if (facts[def]?) {
                messages += { error("Unresolved type for `<u has id ? u.id : u.ids>`", u.occ)};
              }
          }
       }
    
       for(Key l <- sort(domain(calculators), bool(Key a, Key b) { return a.length < b.length; })){
           calc = calculators[l];
           if(!alreadyReported(messages, calc.src)){
              deps = calc.dependsOn;
              forDeps = isEmpty(deps) ? "" : " for <for(int i <- index(deps)){><facts[deps[i]]? ? "`<prettyPrintAType(facts[deps[i]])>`" : "`unknown type of <deps[i]>`"><i < size(deps)-1 ? "," : ""> <}>";
              messages += error("Type of <calc.cname> could not be computed<forDeps>", calc.src);
           }
       }
       
       tmodel.calculators = calculators;
       tmodel.openReqs = openReqs;
  
       for(req <- openReqs, !alreadyReported(messages, req.src)){
           messages += error("Invalid <req.rname>; type of one or more subparts could not be inferred", req.src);
       }
   
       if(cdebug){
           //println("----");
           println("iterations: <iterations>; calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
           printState();
           if(size(calculators) > 0){
               println("Unresolved calculators:");
               for(c <- calculators){
                    calc = calculators[c];
                    println("\t<calc.cname> at <calc.src>:");
                    for(atype <- calc.dependsOn){
                        println("\t  dependsOn: <atype><facts[atype]? ? "" : " ** unavailable **">");
                    }
               }
           }
           
           //println("----");
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
       tmodel.facts = facts;
       tmodel.messages = sortMostPrecise([*messages]);
       
       // Clear globals, to be sure
       facts = ();
       openFacts = {};
       bindings = ();
       openReqs = {};
       messages = {};
       triggersRequirement = ();
       triggersFact = ();
       requirementJobs = {};
    
       if(cdebug) println("Derived facts: <size(tmodel.facts)>");
       return tmodel;
}

// Utilities on TModels that can help to build IDE-features


rel[loc, loc] getUseDef(TModel tmodel){
    res = {};
    for(Use u <- tmodel.uses){
        try {
           foundDefs =  lookup(tmodel, u);
           res += { <u.occ, def> | def <- foundDefs };
        } catch NoKey(): {
            ;// ignore it
        } catch AmbiguousDefinition(_):{
            ;// ignore it
        }
    };
    return res;
}

set[str] getVocabulary(TModel tmodel)
    = {d.id | Define d <- tmodel.defines};

map[loc, AType] getFacts(TModel tmodel)
    = tmodel.facts;

list[Message] getMessages(TModel tmodel)
    = tmodel.messages;