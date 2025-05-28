@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::Collector

/*
    Implementation of the ICollector interface; this is the API of TypePal's fact and constraint collector
*/

import Node;
import Map;
import ParseTree;
import Set;
import Relation;
import IO;
import Type;
import Location;
import String;

import analysis::typepal::Version;
import analysis::typepal::Messenger;

extend analysis::typepal::ConfigurableScopeGraph;
extend analysis::typepal::ICollector;

// Extract (nested) tree locations and type variables from a list of dependencies
list[loc] dependenciesAslocList(list[value] dependencies){
    return
        for(value d <- dependencies){
            if(Tree t := d){
                append getLoc(t);
            } else if(tvar(loc tv) := d){
                append tv;
            } else {
                throw TypePalUsage("Dependency should be a tree or type variable, found <d>");
            }
        };
}

bool isTypeVarFree(AType t){
    if(/tvar(loc _) := t)
        return false;
    else
        return true;
}

list[loc] dependenciesAslocs(list[Tree] dependencies)
    = dependenciesAslocList(dependencies);

// Definition info used during type checking
data DefInfo
    = defType(loc src)
    | defType(Tree tree)
    | defType(AType atype)
    | defTypeCall(list[loc] dependsOn, AType(Solver s) getAType)                           // AType given as callback.
    | defTypeLub(list[loc] dependsOn, list[loc] defines, list[AType(Solver s)] getATypes)   // redefine previous definition
    ;

DefInfo defType(list[Tree] dependsOn, AType(Solver s) getAType){
    return defTypeCall(dependenciesAslocList(dependsOn), getAType);
}

list[loc] getDependencies(defType(loc src))
    = [src];
list[loc] getDependencies(defType(Tree tree))
    = [getLoc(tree)];
list[loc] getDependencies(defType(AType atype))
    = [];
default list[loc] getDependencies(DefInfo di)
    =  di.dependsOn; //di has defines ? di.dependsOn - di.defines : di.dependsOn;

DefInfo defLub(list[Tree] dependsOn, AType(Solver s) getAType)
    = defTypeLub(dependenciesAslocs(dependsOn), [], [getAType]);

// The basic ingredients for type checking: requirements and calculators

void printDeps(list[loc] dependsOn, str indent, map[loc,AType] facts){
    if(isEmpty(dependsOn)){
        println("<indent>  dependsOn: nothing");
    } else {
        for(dep <- dependsOn){
            println("<indent>  dependsOn: <dep><facts[dep]? ? "" : " ** unavailable **">");
        }
    }
}

// A named requirement for location src, given dependencies and a callback predicate
// Eager requirements are tried when not all dependencies are known.
data Requirement(bool eager = false)
    = req(str rname, loc src,  list[loc] dependsOn, void(Solver s) preds)
    | reqEqual(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)
    | reqComparable(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)
    | reqSubtype(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)
    | reqUnify(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)
    | reqError (loc src, list[loc] dependsOn, FailMessage fm)
    | reqErrors(loc src, list[loc] dependsOn, list[FailMessage] fms)
    ;

loc getReqSrc(Requirement req){
    if(req has src) return req.src;
    return req.dependsOn[0];
}

void print(req(str rname, loc src,  list[loc] dependsOn, void(Solver s) preds), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <src>:");
    if(full) printDeps(dependsOn, indent, facts);
}

void print(req(str rname, loc src,  list[loc] dependsOn, void(Solver s) preds), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <src>");
}

void print(reqEqual(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0] ? "no dependencies">");
    if(full) printDeps(dependsOn, indent, facts);
}
void print(reqComparable(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0] ? "no dependencies">");
    if(full) printDeps(dependsOn, indent, facts);
}

void print(reqSubtype(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0] ? "no dependencies">");
    if(full) printDeps(dependsOn, indent, facts);
}

void print(reqUnify(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0] ? "no dependencies">");
    if(full) printDeps(dependsOn, indent, facts);
}

void print(reqError (loc src, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ for <src>");
    if(full) printDeps(dependsOn, indent, facts);
}

void print(reqErrors(loc src, list[loc] dependsOn, list[FailMessage] fms), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ for <src>");
   if(full) printDeps(dependsOn, indent, facts);
}

// Named type calculator for location src, given args, and resolve callback
// Eager calculators are tried when not all dependencies are known.
data Calculator
    = calcType(loc src, AType atype)
    | calcLoc(loc src, list[loc] dependsOn)
    | calc(str cname, loc src, list[loc] dependsOn, AType(Solver s) getAType, bool eager=false)
    | calcLub(str cname, list[loc] srcs, list[loc] dependsOn, list[AType(Solver s)] getATypes, bool eager=false)
    ;

list[loc] dependsOn(Calculator calc){
    return calc has dependsOn ? calc.dependsOn : [];
}

list[loc] srcs(Calculator calc){
    return calc has src ? [calc.src] : calc.srcs;
}

void print(calcType(loc src, AType atype), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>calc <src> as <atype>");
}

void print(calcLoc(loc src, list[loc] dependsOn), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>calc <src> same type as <dependsOn>");
}

void print(calc(str cname, loc src, list[loc] dependsOn, AType(Solver s) calculator), str indent, map[loc,AType] facts, bool full=true){
    print("<indent>calc `<cname>` for <src> using "); iprintln(calculator);
    if(full) printDeps(dependsOn, indent, facts);
}

void print(calcLub(str cname, list[loc] srcs, list[loc] dependsOn, list[AType(Solver s)] getATypes), str indent, map[loc,AType] facts, bool full=true){
    print("<indent>calc lub `<cname>` for <srcs> using "); iprintln(getATypes);
    if(full) printDeps(dependsOn, indent, facts);
}

void print(tuple[loc scope, str id, IdRole idRole, loc defined, DefInfo defInfo] def, str indent, map[loc, AType] facts, bool full=true){
    println("<indent>def: `<def.id>` as <def.idRole> at <def.defined>");
    if(full) printDeps(getDependencies(def.defInfo), indent, facts);
}

Collector defaultCollector(Tree t) = newCollector("defaultModel", t, tconfig());

Collector newCollector(str modelName, Tree pt, TypePalConfig config){
    return newCollector(modelName, (modelName : pt), config);
}

// The following function can be written with a single (expensive) visit
// This version avoids visits as much as possible
private TModel convertLocs(TModel tm, map[loc,loc] locMap){
    defines = {};
    definitions = ();
    for(d:<loc scope, str _, str _, IdRole _, loc defined, DefInfo defInfo> <- tm.defines){
        defi = visit(defInfo){ case loc l => locMap[l] when l in locMap };
        d1 = d[scope=(scope in locMap ? locMap[scope] : scope)]
               [defined=(defined in locMap ? locMap[defined] : defined)]
               [defInfo=defi];
        defines += d1;
        definitions[d1.defined] = d1;
    }
    tm.defines = defines;
    tm.definitions = definitions;

    tm.scopes = ( (outer in locMap ? locMap[outer] : outer) : (inner in locMap ? locMap[inner] : inner) 
                | loc outer <- tm.scopes, loc inner := tm.scopes[outer] 
                );
    tm.paths = { <(from in locMap ? locMap[from] : from), 
                  pathRole, 
                  (to in locMap ? locMap[to] : to)> 
               | <loc from, PathRole pathRole, loc to> <- tm.paths 
               };

    tm.referPaths =  visit(tm.referPaths){ case loc l => locMap[l] when l in locMap };
    tm.uses = visit(tm.uses){ case loc l => locMap[l] when l in locMap };
    tm.definesMap = visit(tm.definesMap){ case loc l => locMap[l] when l in locMap };
    tm.moduleLocs = ( key : (l in locMap ? locMap[l] : l) 
                    | key <- tm.moduleLocs, l := tm.moduleLocs[key] 
                    );
    facts = tm.facts;
    tm.facts = ((l in locMap ? locMap[l] : l) 
               : ( (overloadedAType(rel[loc, IdRole, AType] overloads) := atype)
                   ? overloadedAType({ <(l in locMap ? locMap[l] : l), idr, at> | <l, idr, at> <- overloads })
                   : atype)
               | l <- facts, atype := facts[l]
               );
    //tm.facts = visit(tm.facts){ case loc l => locMap[l] ? l };
    tm.specializedFacts =
        ((l in locMap ? locMap[l] : l)
         : ( (overloadedAType(rel[loc, IdRole, AType] overloads) := atype)
             ? overloadedAType({ <(l in locMap ? locMap[l] : l), idr, at> | <l, idr, at> <- overloads })
             : atype)
        | l <- tm.specializedFacts, atype := tm.specializedFacts[l]
        );
    //tm.specializedFacts = visit(tm.specializedFacts){ case loc l => locMap[l] ? l };
    tm.useDef = { < (f in locMap ? locMap[f] : f), 
                    (t in locMap ? locMap[t] : t) > 
                | <f, t> <- tm.useDef };
    // Exlude messages from conversion: otherwise users would see logical locations
    //tm.messages =  visit(tm.messages){ case loc l => locMap[l] ? l };
    tm.store =  visit(tm.store){ case loc l => locMap[l] when l in locMap};
    tm.config = visit(tm.config){ case loc l => locMap[l] when l in locMap};
    return tm;
}

TModel convertTModel2PhysicalLocs(TModel tm){
    if(!tm.usesPhysicalLocs){
        logical2physical = tm.logical2physical;
        tm.logical2physical = ();
        tm = convertLocs(tm, logical2physical);
        tm.logical2physical = logical2physical;
        tm.usesPhysicalLocs = true;
    }
    return tm;
}

TModel convertTModel2LogicalLocs(TModel tm, map[str,TModel] tmodels){
    if(tm.usesPhysicalLocs){
        tmodels[tm.modelName] = tm;
        physical2logical = ();
        try {
            physical2logical = invertUnique((() | it + tm1.logical2physical | tm1 <- range(tmodels)));
        } catch MultipleKey(value physLoc, value _, value _):{
            where = loc l := physLoc ? l : |unknown:///|;
            // find the offending modules
            mnames = {};
            for(mname <- domain(tmodels)){
                if(physLoc in range(tmodels[mname].logical2physical)){
                    mnames += mname;
                }
            }
            tm.messages += [error("Please recheck modules <intercalateAnd(toList(mnames))>; their mapping from physical to logical locations is outdated", where)];
            return tm;
        }
        logical2physical = tm.logical2physical;
        tm.logical2physical = ();
        tm = convertLocs(tm, physical2logical);
        tm.logical2physical = logical2physical;
        tm.usesPhysicalLocs = false;
    }
    return tm;
}

Collector newCollector(str modelName, map[str,Tree] namedTrees, TypePalConfig config){

    str normalizeName(str input) {
            return config.normalizeName(input);
         }
    loc globalScope = |global-scope:///|;
    Defines defines = {};

    map[loc,loc] logical2physical = ();
    map[loc, set[Define]] definesPerLubScope = (globalScope: {});
    map[loc, set[Define]] lubDefinesPerLubScope = (globalScope: {});
    map[loc, rel[str id, str orgId, loc idScope, set[IdRole] idRoles, loc occ]] lubUsesPerLubScope = (globalScope: {});
    map[loc, rel[loc,loc]]  scopesPerLubScope = (globalScope: {});

    Scopes scopes = ();
    map[loc, set[loc]] scopesStar = (globalScope: {});

    Paths paths = {};
    set[ReferPath] referPaths = {};
    Uses uses = [];
    map[str,value] storeVals = ();

    map[loc,AType] facts = ();
    set[Calculator] calculators = {};
    set[Requirement] requirements = {};
    int ntypevar = 0;
    list[Message] messages = [];

    loc currentScope = globalScope;
    loc rootScope = globalScope;

    for(nm <- namedTrees) scopes[getLoc(namedTrees[nm])] = globalScope;
    lrel[loc scope, bool lubScope, map[ScopeRole, value] scopeInfo] scopeStack = [<globalScope, false, (anonymousScope(): false)>];
    list[loc] lubScopeStack = [];
    loc currentLubScope = globalScope;
    int nPredefinedTree = 0;

    bool building = true;

    void collector_define(str orgId, IdRole idRole, value def, DefInfo info){
        if(building){
            loc l = |undefined:///|;
            if(Tree tdef := def) l = getLoc(tdef);
            else if(loc ldef := def) l = ldef;
            else throw TypePalUsage("Argument `def` of `define` should be `Tree` or `loc`, found <typeOf(def)>");

            def_tup = <orgId, idRole>;
            nname = normalizeName(orgId);

            if(info is defTypeLub){
                // Look for an outer variable declaration of id that overrules the defTypeLub
                for(Define def <- defines + definesPerLubScope[currentLubScope]){
                    if(def.id == nname && config.isInferrable(def.idRole)){
                        if(def.scope in scopeStack<0>) {
                            uses += use(nname, orgId, l, currentScope, {def.idRole});
                            return;
                        }
                    }
                }
                lubDefinesPerLubScope[currentLubScope] += <currentScope, nname, orgId, idRole, l, info>;
            } else {
                definesPerLubScope[currentLubScope] += <currentScope, nname, orgId, idRole, l, info>;
            }
        } else {
            throw TypePalUsage("Cannot call `define` on Collector after `run`");
        }
    }

    Tree collector_predefine(str id, IdRole idRole, value def, DefInfo info){
        l = collector_getPredefinedTree(def, id);
        collector_define(id, idRole, l, info);
        return l;
    }

    Tree collector_predefineInScope(value scope, str id, IdRole idRole, DefInfo info){
        l = collector_getPredefinedTree(scope, id);
        collector_defineInScope(scope, id, idRole, l, info);
        return l;
    }

    Tree collector_getPredefinedTree(value scope, str id){

        loc defining = |undefined:///|;
        if(Tree tdef := scope) defining = getLoc(tdef);
        else if(loc ldef := scope) defining = ldef;
        else throw TypePalUsage("Argument `scope` should be `Tree` or `loc`, found <typeOf(scope)>");

        nPredefinedTree += 1;
        return appl(prod(sort("$PREDEFINED-<id>"), [], {}),
                    [])[@\loc=defining[query="predefined=<id>"][fragment="<nPredefinedTree>"]];
    }

    bool collector_isAlreadyDefined(str id,  Tree useOrDef){

        lubdefs = { def | def <- definesPerLubScope[currentLubScope], def.id == id } +
                  { def | def <- lubDefinesPerLubScope[currentLubScope], def.id == id };
        useOrDefLoc = getLoc(useOrDef);

        if(!isEmpty(lubdefs) && any(def <- lubdefs, isContainedIn(useOrDefLoc, def.scope))){
            return true;
        }

        for(def <- defines, def.id == id, isContainedIn(useOrDefLoc, def.scope)){
            return true;
        }
        return false;
    }

    void collector_defineInScope(value scope, str orgId, IdRole idRole, value def, DefInfo info){
        if(building){
            loc definingScope = |undefined:///|;
            if(Tree tscope := scope) definingScope = getLoc(tscope);
            else if(loc lscope := scope) definingScope = lscope;
            else throw TypePalUsage("Argument `scope` of `defineInScope` should be `Tree` or `loc`, found <typeOf(scope)>");

            loc l = |undefined:///|;
            if(Tree tdef := def) l = getLoc(tdef);
            else if(loc ldef := def) l = ldef;
            else throw TypePalUsage("Argument `def` of `defineInScope` should be `Tree` or `loc`, found <typeOf(def)>");

            nname = normalizeName(orgId);
            if(info is defTypeLub){
                throw TypePalUsage("`defLub` cannot be used in combination with `defineInScope`");
            } else {
                defines += <definingScope, nname, orgId, idRole, /*uid,*/ l, info>;
            }
        } else {
            throw TypePalUsage("Cannot call `defineInScope` on Collector after `run`");
        }
    }

    void collector_use(Tree occ, set[IdRole] idRoles) {
        if(building){
           orgId = "<occ>";
           uses += use(normalizeName(orgId), orgId, getLoc(occ), currentScope, idRoles);
        } else {
            throw TypePalUsage("Cannot call `use` on Collector after `run`");
        }
    }

    void collector_useLub(Tree occ, set[IdRole] idRoles) {
        if(building){
           lubUsesPerLubScope[currentLubScope] += <normalizeName("<occ>"), "<occ>", currentScope, idRoles, getLoc(occ)>;
        } else {
            throw TypePalUsage("Cannot call `useLub` on Collector after `run`");
        }
    }

    void collector_addPathToDef(Tree occ, set[IdRole] idRoles, PathRole pathRole) {
        if(building){
            orgId = "<occ>";
            u = use(normalizeName(orgId), orgId, getLoc(occ), currentScope, idRoles);
            uses += u;
            referPaths += referToDef(u, pathRole);
        } else {
            throw TypePalUsage("Cannot call `collector_addPathToDef` on Collector after `run`");
        }
    }

    AType(Solver) makeGetTypeInType(Tree container, Tree selector, set[IdRole] idRolesSel, loc scope){
        return AType(Solver s) {
            return s.getTypeInType(s.getType(container), selector, idRolesSel, scope);
         };
    }

    void collector_useViaType(Tree container, Tree selector, set[IdRole] idRolesSel){
        if(building){
            name = normalizeName("<selector>");
            sloc = getLoc(selector);
            calculators += calc("useViaType `<name>` in <getLoc(container)>", sloc,  [getLoc(container)],  makeGetTypeInType(container, selector, idRolesSel, currentScope));
        } else {
            throw TypePalUsage("Cannot call `useViaType` on Collector after `run`");
        }
    }

    void collector_useQualified(list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles){
        if(building){
           uses += useq([normalizeName(id) | id <- ids], "<occ>", getLoc(occ), currentScope, idRoles, qualifierRoles);
        } else {
            throw TypePalUsage("Cannot call `useQualified` on Collector after `run`");
        }
     }

     void collector_addPathToQualifiedDef(list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathRole pathRole){
        if(building){
            u = useq([normalizeName(id) | id <- ids], "<occ>", getLoc(occ), currentScope, idRoles, qualifierRoles);
            uses += u;
            referPaths += referToDef(u, pathRole);
        } else {
            throw TypePalUsage("Cannot call `addPathToQualifiedDef` on Collector after `run`");
        }
    }

    void collector_addPathToType(Tree occ, PathRole pathRole){
         if(building){
            referPaths += referToType(getLoc(occ), currentScope, pathRole);
        } else {
            throw TypePalUsage("Cannot call `addPathToType` on Collector after `run`");
        }
    }

    void collector_enterScope(Tree inner){
        enterScope(getLoc(inner));
    }

    void collector_enterCompositeScope(list[Tree] trees){
        enterScope(cover([getLoc(t) | t <- trees]));
    }

    void collector_enterLubScope(Tree inner){
        enterScope(getLoc(inner), lubScope=true);
    }

    void collector_enterCompositeLubScope(list[Tree] trees){
        enterScope(cover([getLoc(inner) | inner <- trees]), lubScope=true);
    }

    void enterScope(loc innerLoc, bool lubScope=false){
        if(building){
            if(innerLoc == rootScope){
              currentScope = innerLoc;
              scopeStack = push(<innerLoc, lubScope, ()>, scopeStack);
              scopesStar[currentScope] = {currentScope};
           } else {
              scopes[innerLoc] = currentScope;
              scopesStar[innerLoc] = scopesStar[currentScope] + innerLoc;
              scopesPerLubScope[currentLubScope] += <currentScope, innerLoc>;
              currentScope = innerLoc;
              scopeStack = push(<innerLoc, lubScope, ()>, scopeStack);
              if(lubScope && isEmpty(lubScopeStack)){   // Nested lubScopes are merged in outer lubScope
                lubScopeStack = push(innerLoc, lubScopeStack);
                currentLubScope = innerLoc;
                definesPerLubScope[currentLubScope] = {};
                lubDefinesPerLubScope[currentLubScope] = {};
                lubUsesPerLubScope[currentLubScope] = {};
                scopesPerLubScope[currentLubScope] = {};
              }
           }
        } else {
          throw TypePalUsage("Cannot call `enterScope` on Collector after `run`");
        }
    }

    void collector_leaveScope(Tree inner){
        leaveScope(getLoc(inner));
    }

    void collector_leaveCompositeScope(list[Tree] trees){
        leaveScope(cover([getLoc(t) | t <- trees]));
    }

    void leaveScope(loc innerLoc){
        if(building){
           if(innerLoc == currentScope){
              scopeStack = tail(scopeStack);
              if(isEmpty(scopeStack)){
                 throw TypePalUsage("Cannot call `leaveScope` beyond the root scope");
              }
              currentScope = scopeStack[0].scope;
              if(!isEmpty(lubScopeStack) && innerLoc == lubScopeStack[0]){
                extraDefs = finalizeDefines(currentLubScope);
                defines += extraDefs;
                lubScopeStack = tail(lubScopeStack);
                if(isEmpty(lubScopeStack)){
                   currentLubScope = globalScope;
                } else {
                   currentLubScope = lubScopeStack[0];
                }
              }
           } else {
              throw TypePalUsage("Cannot call `leaveScope` with scope that is not the current scope", [innerLoc]);
           }
        } else {
          throw TypePalUsage("Cannot call `leaveScope` on Collector after `run`");
        }
    }

    void collector_setScopeInfo(loc scope, ScopeRole scopeRole, value scopeInfo){
        if(building){
           for(int i <- index(scopeStack), <scope, lubScope, map[ScopeRole,value] scopeInfo2> := scopeStack[i]){
               scopeInfo2[scopeRole] = scopeInfo;
               //scopeStack[i] = <scope, lubScope, scopeInfo2>; TODO: why does this not work?
               if(i == 0){
                  scopeStack =  <scope, lubScope, scopeInfo2> + tail(scopeStack);
               } else {
                 scopeStack =  scopeStack[0..i] + [<scope, lubScope, scopeInfo2>] + scopeStack[i+1..];
               }
               return;
           }
           throw TypePalUsage("`setScopeInfo` scope cannot be found");
        } else {
           throw TypePalUsage("Cannot call `setScopeInfo` on Collector after `run`");
        }
    }

    lrel[loc scope, value scopeInfo] collector_getScopeInfo(ScopeRole scopeRole){
        if(building){
            res =
                for(<loc scope, _, map[ScopeRole,value] scopeInfo> <- scopeStack, scopeRole in scopeInfo){
                    append <scope, scopeInfo[scopeRole]>;
                }
            return res;
        } else {
           throw TypePalUsage("Cannot call `getScopeInfo` on Collector after `run`");
        }
    }

    loc collector_getScope(){
        if(building){
            return currentScope;
        } else {
            throw TypePalUsage("Cannot call `getScope` on Collector after `run`");
        }
    }

    void collector_require(str name, Tree src, list[value] dependencies, void(Solver s) preds){
        if(building){
           requirements += req(name, getLoc(src), dependenciesAslocList(dependencies), preds);
        } else {
            throw TypePalUsage("Cannot call `require` on Collector after `run`");
        }
    }

    void collector_requireEager(str name, Tree src, list[value] dependencies, void(Solver s) preds){
        if(building){
           requirements += req(name, getLoc(src), dependenciesAslocList(dependencies), preds, eager=true);
        } else {
            throw TypePalUsage("Cannot call `require` on Collector after `run`");
        }
    }

    list[loc] getDeps(value l, value r){
        if(AType _ := l){
           return Tree rtree := r ? [getLoc(rtree)] : [];
        }
        return AType _ := r ? [getLoc(l)] : [getLoc(l), getLoc(r)];
    }

    value getLocIfTree(value v) = Tree tree := v ? getLoc(tree) : v;

    void collector_requireEqual(value l, value r, FailMessage fm){
        if(building){
           requirements += reqEqual("`<l>` requireEqual `<r>`", getLocIfTree(l), getLocIfTree(r), getDeps(l, r), fm);
        } else {
            throw TypePalUsage("Cannot call `requireEqual` on Collector after `run`");
        }
    }

    void collector_requireComparable(value l, value r, FailMessage fm){
        if(building){
           requirements += reqComparable("`<l>` requireEqual `<r>`", getLocIfTree(l), getLocIfTree(r), getDeps(l, r), fm);
        } else {
            throw TypePalUsage("Cannot call `requireComparable` on Collector after `run`");
        }
    }

    void collector_requireSubType(value l, value r, FailMessage fm){
        if(building){
           requirements += reqSubtype("`<l>` requireSubType `<r>`", getLocIfTree(l), getLocIfTree(r), getDeps(l, r), fm);
        } else {
            throw TypePalUsage("Cannot call `requireSubType` on Collector after `run`");
        }
    }

    void collector_requireUnify(value l, value r, FailMessage fm){
        if(building){
           requirements += reqUnify("`<l>` requireUnify `<r>`", getLocIfTree(l), getLocIfTree(r), getDeps(l, r), fm);
        } else {
            throw TypePalUsage("Cannot call `requireUnify` on Collector after `run`");
        }
    }

    bool isValidReplacement(AType old, AType new){
        if(tvar(_) := old) return true;
        try {
            return old == new || config.isSubType(old, new) || config.isSubType(new, old);
        } catch value _:
            return false;
    }

    void collector_fact(Tree tree, value tp){
        if(building){
          srcLoc = getLoc(tree);
          if(AType atype := tp){
            if(isTypeVarFree(atype)) {
                if(srcLoc in facts && !isValidReplacement(facts[srcLoc], atype)){
                    println("Double fact declaration for <srcLoc>: <facts[srcLoc]> != <atype>");
                } else {
                    facts[srcLoc] = atype;
                }
            } else {
                calculators += calcType(srcLoc, atype);
            }
          } else if(Tree tree2 := tp){
            fromLoc = getLoc(tree2);
            if(srcLoc != fromLoc){
                if(fromLoc in facts){
                    fromType = facts[fromLoc];
                    if(srcLoc in facts && !isValidReplacement(facts[srcLoc], fromType)){
                        println("Double fact declaration for <srcLoc>: <facts[srcLoc]> != <fromType>");
                    } else {
                        facts[srcLoc] = facts[fromLoc];
                    }
                } else {
                    calculators += calcLoc(srcLoc, [fromLoc]);
                }
            }
          } else {
            throw TypePalUsage("Argument of `fact` should be `AType` or `Tree`, found `<typeOf(tp)>` at <srcLoc>");
          }
        } else {
            throw TypePalUsage("Cannot call `fact` on Collector after `run`");
        }
    }

    AType collector_getType(Tree tree){
        if(building){
            srcLoc = getLoc(tree);
            if(srcLoc in facts) return facts[srcLoc];
            throw TypeUnavailable();
        } else {
            throw TypePalUsage("Cannot call `getType` on Collector after `run`");
        }
    }

    void collector_calculate(str name, Tree src, list[value] dependencies, AType(Solver s) calculator){
        if(building){
           srcLoc = getLoc(src);
           calculators += calc(name, srcLoc, dependenciesAslocList(dependencies) - srcLoc, calculator);
        } else {
            throw TypePalUsage("Cannot call `calculate` on Collector after `run`");
        }
    }

    void collector_calculateEager(str name, Tree src, list[value] dependencies, AType(Solver s) calculator){
        if(building){
           srcLoc = getLoc(src);
           calculators += calc(name, srcLoc, dependenciesAslocList(dependencies) - srcLoc, calculator, eager=true);
        } else {
            throw TypePalUsage("Cannot call `calculateEager` on Collector after `run`");
        }
    }

    bool collector_report(FailMessage fm){
       if(building){
            loc sloc = |unknown:///|;
            if(loc l := fm.src) sloc = l;
            else if(Tree t := fm.src) sloc = getLoc(t);
            else throw TypePalUsage("Subject in error should be have type `Tree` or `loc`, found <typeOf(fm.src)>");
          requirements += reqError(sloc, [], fm);
          return true;
       } else {
            throw TypePalUsage("Cannot call `report` on Collector after `run`");
       }
    }

     bool collector_reports(list[FailMessage] fms){
       if(building){
            fm = getFirstFrom(fms);
            loc sloc = |unknown:///|;
            if(loc l := fm.src) sloc = l;
            else if(Tree t := fm.src) sloc = getLoc(t);
            else throw TypePalUsage("Subject in error should be have type `Tree` or `loc`, found <typeOf(fm.src)>");
          requirements += reqErrors(sloc, [], fms);
          return true;
       } else {
            throw TypePalUsage("Cannot call `reports` on Collector after `run`");
       }
    }

    AType collector_newTypeVar(value src){
        if(building){
            tvLoc = |unknown:///|;
            if(Tree _ := src){
                tvLoc = getLoc(src);
            } else if(loc l := src){
                tvLoc = l;
            } else {
                throw TypePalUsage("`newTypeVar` requires argument of type `Tree` or `loc`");
            }
            tvLoc.fragment = "<ntypevar>";
            ntypevar += 1;
            tv = tvar(tvLoc);
            return tv;
        } else {
            throw TypePalUsage("Cannot call `newTypeVar` on Collector after `run`");
        }
    }

    void collector_push(str key, value val){
        if(key in storeVals && list[value] old := storeVals[key]){
           storeVals[key] = val + old;
        } else {
           storeVals[key] = [val];
        }
    }

    value collector_pop(str key){
        if(key in storeVals && list[value] old := storeVals[key], size(old) > 0){
           pval = old[0];
           storeVals[key] = tail(old);
           return pval;
        } else {
           throw TypePalUsage("Cannot pop from empty stack for key `<key>`");
        }
    }

    value collector_top(str key){
        if(key in storeVals && list[value] old := storeVals[key], size(old) > 0){
           return old[0];
        } else {
           throw TypePalUsage("Cannot get top from empty stack for key `<key>`");
        }
    }

    list[value] collector_getStack(str key){
        if(key in storeVals && list[value] old := storeVals[key]){
            return old;
        }
        return [];
    }

    void collector_clearStack(str key){
        storeVals[key] = [];
    }

    TypePalConfig collector_getConfig(){
        return config;
    }

    void collector_setConfig(TypePalConfig cfg){
        config = cfg;
    }

    // Compute dependencies and defs for one LubDef:
    // - Remove dependencies with a nested use in order to break cycles (but add them as defs)
    // - Add all uses that are in scope as defs

    tuple[list[loc] deps, list[loc] defs] computeDepsAndDefs(set[loc] deps, set[loc] defs, set[Use] uses, loc lubDefScope, rel[loc,loc] enclosedScopes){
        if(isEmpty(uses)) return <toList(deps - defs), toList(defs)>;
        depsWithNestedUse = { d | d <- deps, u <- uses, isContainedIn(u.occ, d) };
        scopesEnclosedByLubDef = enclosedScopes[lubDefScope];
        return <toList(deps - defs - depsWithNestedUse), toList(defs + depsWithNestedUse + { u.occ | u <- uses, u.scope in scopesEnclosedByLubDef })>;
    }

    bool isDefinedBefore(Define a, Define b)
        = isBefore(a.defined, b.defined);

    // Merge all LubDefs and appoint a definition to refer to
    // When LubDefs in disjoint scopes are encountered they will be merged into separate defines

    set[Define] mergeLubDefs(str id, loc scope, set[Define] lubDefs,  set[Use] uses, rel[loc,loc] enclosedScopes){
        set[Define] mergedDefs = {};
        sortedLubDefs = sort(lubDefs, isDefinedBefore);
        Define firstDefine = sortedLubDefs[0];

        set[loc] deps = {}; getATypes = [];
        defineds = {};
        set[IdRole] roles = {};

        for(def <- sortedLubDefs){
            if(def != firstDefine && def.scope notin enclosedScopes[firstDefine.scope]){
                mergedDefs += {<firstDefine.scope, id, id, role, firstDefine.defined, defTypeLub(ldeps, ldefs, getATypes)> | role <- roles, <ldeps, ldefs> := computeDepsAndDefs(deps, defineds, uses, firstDefine.scope, enclosedScopes)};
                deps = {}; getATypes = [];
                defineds = {};
                roles = {};
                firstDefine = def;
            }
            roles += def.idRole;
            defineds += def.defined;
            deps += toSet(def.defInfo.dependsOn);
            getATypes += def.defInfo.getATypes;
        }
        mergedDefs += {<scope, id, id, role, firstDefine.defined, defTypeLub(ldeps, ldefs, getATypes)> | role <- roles, <ldeps, ldefs> := computeDepsAndDefs(deps, defineds, uses, firstDefine.scope, enclosedScopes)};
        return mergedDefs;
    }

    // Is there a fixed (i.e. non-LubDef) define in an outer scope?

    bool existsFixedDefineInOuterScope(str id, loc lubScope){
        outer = lubScope;
        while(outer in scopes && scopes[outer] != |global-scope:///|){
            outer = scopes[outer];
            for(<loc _, id, _, idRole, loc _, DefInfo _> <- definesPerLubScope[outer] ? {}, config.isInferrable(idRole)){
                return true;
            }
        }
        return false;
    }

    // Finalize the defines by adding lubDefs in the global scope

     set[Define] finalizeDefines(){
        return defines + definesPerLubScope[globalScope];
     }

    //  Finalize all defLubs and useLubs in one lubScope:
    //  1. A definition with a fixed type in the lubScope itself:
    //     - change all defLubs into uses of that definition
    //  2. A definition (but without a fixed type) in the lubScope itself:
    //     - merge all defLubs (also in nested scopes)
    //  3. Definitions with a fixed type in one or more subscopes:
    //     - change all defLubs per subscope (and its subscopes) to use the definition in the subscope
    //  4. Definitions (but without a fixed type) in one or more subscopes:
    //     - merge all defLubs per subscope (and its subscopes)
    // Recall:
    // alias Define - tuple[loc scope, str id, IdRole idRole, loc defined, DefInfo defInfo];

     set[Define] finalizeDefines(loc lubScope){
        set[Define] extra_defines = {};

        rel[loc,loc] enclosedScopes = scopesPerLubScope[lubScope]* + <lubScope,lubScope>;
        set[loc] allScopes = carrier(enclosedScopes);

        set[Define] deflubs_in_lubscope = lubDefinesPerLubScope[lubScope];
        set[str] deflub_names = deflubs_in_lubscope<1>;
        rel[str id, str orgId, loc idScope, set[IdRole] idRoles, loc occ] uselubs_in_lubscope = lubUsesPerLubScope[lubScope];


        set[Define] local_fixed_defines = definesPerLubScope[lubScope];
        extra_defines += definesPerLubScope[lubScope];

        rel[str, loc] local_fixed_defines_scope = local_fixed_defines<1,0>;
        set[str] ids_with_fixed_def = domain(local_fixed_defines_scope);

        for(str id <- deflub_names){
            set[loc] id_defined_in_scopes = { def.scope | def <- deflubs_in_lubscope, def.id == id };
            set[Use] id_used_in_scopes = {use(tup.tid, tup.orgId, tup.occ, tup.idScope, tup.idRoles) | tuple[str tid, str orgId, loc idScope, set[IdRole] idRoles, loc occ] tup <- uselubs_in_lubscope, tup.tid == id};
            id_defined_in_scopes = { sc1 | loc sc1 <- id_defined_in_scopes, isEmpty(enclosedScopes) || !any(loc sc2 <- id_defined_in_scopes, sc1 != sc2, <sc2, sc1> in enclosedScopes)};

            if({ _ } := local_fixed_defines[lubScope, id]){   // Definition exists with fixed type in the lubScope; Use it instead of the lubDefines
               //println("---top level fixedDef: <fixedDef> in <lubScope>");
               for(def <- deflubs_in_lubscope, def.id == id){
                   u = use(id, id, def.defined, lubScope, {def.idRole});
                   //println("add: <u>");
                   uses += u;
               }
            } else if(existsFixedDefineInOuterScope(id, lubScope)){   // Definition exists with fixed type in a surrounding scope; Use it instead of the lubDefines
               //println("---top level fixedDef: <fixedDef> in <lubScope>");
               for(def <- deflubs_in_lubscope, def.id == id){
                   u = use(id, id, def.defined, lubScope, {def.idRole});
                   //println("add: <u>");
                   uses += u;
               }
            } else if(id in ids_with_fixed_def){ // Definition(s) with fixed type exist in one or more subscopes, use them instead of the lubDefines
                //println("---fixed def(s) in subscopes: <local_fixed_defines_scope[id]>");
                //println("enclosedScopes: <enclosedScopes>");
                for(scope <- allScopes){
                    if(scope in local_fixed_defines_scope[id]){
                        for(def <- deflubs_in_lubscope, def.id == id, def.scope in enclosedScopes[scope]){
                            u = use(id, id, def.defined, scope, {def.idRole});
                            //println("add: <u>");
                            uses += u;
                        }
                    } else {
                        id_dfs = {def | def <- deflubs_in_lubscope, def.id == id, def.scope == scope };
                        if(!isEmpty(id_dfs)) {
                            extra_defines += mergeLubDefs(id, scope, id_dfs, id_used_in_scopes, enclosedScopes);
                        }
                    }
                }
            } else if(lubScope in id_defined_in_scopes){   // Definition exists in the lubScope without fixed type, merge all lubDefs
                //println("---toplevel lubDef");
                 id_dfs = { def | def <- deflubs_in_lubscope, def.id == id, def.scope in enclosedScopes[id_defined_in_scopes] };
                 if(!isEmpty(id_dfs)){
                    extra_defines += mergeLubDefs(id, lubScope, id_dfs, id_used_in_scopes, enclosedScopes);
                 }
           } else {                                     // Same id defined in one or more disjoint subscopes
             for(scope <- id_defined_in_scopes){
                if({ _ } := local_fixed_defines[scope, id]){ // defined in outer scope with fixed type
                   //println("fixedDef: <fixedDef> in inner scope <scope>");
                   // There exists a definition with fixed type in the inner scope, just use it instead of the lubDefines
                   for(def <- deflubs_in_lubscope, def.id == id, def.scope in enclosedScopes[id_defined_in_scopes]){
                       u = use(id, id, def.defined, scope, {def.idRole});
                      //println("add: <u>");
                       uses += u;
                   }
               } else {
                 extra_defines += mergeLubDefs(id, scope, {def | def <- deflubs_in_lubscope, def.id == id, def.scope in enclosedScopes[scope]}, id_used_in_scopes, enclosedScopes);
               }
             }
           }
        }

        // Transform uncovered lubUses into ordinary uses

        for(u: <str id, str orgId, loc idScope, set[IdRole] idRoles, loc occ> <- uselubs_in_lubscope){
            //println("replace lubUse by <use(id, occ, idScope, idRoles)>");
            uses += use(id, orgId, occ, idScope, idRoles);
            uselubs_in_lubscope -= u;
        }

        definesPerLubScope = Map::delete(definesPerLubScope, lubScope);   // Remove all data recorded for this lubScope
        lubDefinesPerLubScope = Map::delete(lubDefinesPerLubScope, lubScope);
        lubUsesPerLubScope = Map::delete(lubUsesPerLubScope, lubScope);
        scopesPerLubScope = Map::delete(scopesPerLubScope, lubScope);

        return extra_defines;
    }

    // We don't convert here logical/physical locations and just reuse
    void collector_addTModel(TModel tm){
        if(!isValidTplVersion(tm.version)){
            throw wrongTplVersion("TModel for <tm.modelName> uses TPL version <tm.version>, but <getCurrentTplVersion()> is required");
        }
        tm = convertTModel2PhysicalLocs(tm);

        logical2physical += tm.logical2physical;
        messages += tm.messages;

        scopes += tm.scopes;
        defines += tm.defines;
        facts += tm.facts;
        paths += tm.paths;
    }

    map[loc,loc] buildLogical2physical(Defines defines){
        map[loc,loc] my_logical2physical = logical2physical;
        map[loc,loc] my_physical2logical = ();
        try {
            my_physical2logical = invertUnique(logical2physical);
        } catch MultipleKey(value key, value _first, value _second):{
            where = loc l := key ? l : |unknown:///|;
            messages += error("Mapping from physical to logical locations is not unique; remove outdated information and try again", where);
            return ();
        }
        for(Define def <- defines){
            logicalLoc = my_physical2logical[def.defined] ? config.createLogicalLoc(def, modelName, config.typepalPathConfig);
            if(logicalLoc != def.defined){
                if(logicalLoc in my_logical2physical){
                    if(my_logical2physical[logicalLoc] != def.defined){
                        messages += error("Remove code clone for <prettyRole(def.idRole)> `<def.id>` at <my_logical2physical[logicalLoc]> and <def.defined>", def.defined);
                    }
                }
                my_logical2physical[logicalLoc] = def.defined;
            }
        }
        return my_logical2physical;
    }

    TModel collector_run(){
        if(building){
           building = false;

           if(size(scopeStack) == 0){
                throw TypePalUsage("Bottom entry missing from scopeStack: more leaveScopes than enterScopes");
           }

           if(size(scopeStack) > 1){
                unclosed = [scope | <loc scope, bool _, map[ScopeRole, value] _> <- scopeStack];
                throw TypePalUsage("Missing `leaveScope`(s): unclosed scopes <unclosed>");
           }

           tm = tmodel()[usesPhysicalLocs=true];
           tm.modelName = modelName;

           tm.moduleLocs = (nm : getLoc(namedTrees[nm]) | nm <- namedTrees);

           tm.facts = facts; facts = ();
           tm.config = config;
           defines = finalizeDefines();
           tm.defines = defines;
           tm.scopes = scopes;  scopes = ();
           tm.paths = paths;
           tm.referPaths = referPaths;
           tm.uses = uses;      uses = [];

           tm.calculators = calculators; calculators = {};
           tm.requirements = requirements;  requirements = {};
           tm.store = storeVals;        storeVals = ();
           tm.definitions = ( def.defined : def | Define def <- defines);
           map[loc, map[str, rel[IdRole idRole, loc defined]]] definesMap = ();
           for(<loc scope, str id, str _orgId, IdRole idRole, loc defined, DefInfo _> <- defines){
                map[str, rel[IdRole idRole, loc defined]] dm = ();
                if(scope in definesMap) dm = definesMap[scope];
                dm[id] =  (dm[id] ? {}) + {<idRole, defined>};
                definesMap[scope] = dm;
           }
           tm.definesMap = definesMap;

           tm.logical2physical = buildLogical2physical(defines);
           defines = {};
           tm.messages = messages;

           return tm;
        } else {
           throw TypePalUsage("Cannot call `run` on Collector after `run`");
        }
    }

    return collector(
        /* Life cycle */    collector_run,

        /* Configure */     collector_getConfig,
                            collector_setConfig,

        /* Scoping */       collector_enterScope,
                            collector_enterCompositeScope,
                            collector_enterLubScope,
                            collector_enterCompositeLubScope,
                            collector_leaveScope,
                            collector_leaveCompositeScope,
                            collector_getScope,

        /* Scope Info */    collector_setScopeInfo,
                            collector_getScopeInfo,

        /* Nested Info */   collector_push,
                            collector_pop,
                            collector_top,
                            collector_getStack,
                            collector_clearStack,

        /* Compose */       collector_addTModel,

        /* Reporting */     collector_report,
                            collector_reports,

        /* Define */        collector_define,
                            collector_defineInScope,
                            collector_predefine,
                            collector_predefineInScope,
                            collector_isAlreadyDefined,

        /* Use */           collector_use,
                            collector_useQualified,
                            collector_useViaType,
                            collector_useLub,

        /* Path */          collector_addPathToDef,
                            collector_addPathToQualifiedDef,
                            collector_addPathToType,

        /* Inference */     collector_newTypeVar,

        /* Fact */          collector_fact,

        /* GetType */       collector_getType,

        /* Calculate */     collector_calculate,
                            collector_calculateEager,

        /* Require */       collector_require,
                            collector_requireEager,
                            collector_requireEqual,
                            collector_requireComparable,
                            collector_requireSubType,
                            collector_requireUnify
                    );
}

// ---- collect utilities -----------------------------------------------------

void collect(Tree t1, Tree t2, Collector c){
    collect(t1, c);
    collect(t2, c);
}

void collect(Tree t1, Tree t2, Tree t3, Collector c){
    collect(t1, c);
    collect(t2, c);
    collect(t3, c);
}

void collect(Tree t1, Tree t2, Tree t3, Tree t4, Collector c){
    collect(t1, c);
    collect(t2, c);
    collect(t3, c);
    collect(t4, c);
}

void collect(Tree t1, Tree t2, Tree t3, Tree t4, Tree t5, Collector c){
    collect(t1, c);
    collect(t2, c);
    collect(t3, c);
    collect(t4, c);
    collect(t5, c);
}

void collect(Tree t1, Tree t2, Tree t3, Tree t4, Tree t5, Tree t6, Collector c){
    collect(t1, c);
    collect(t2, c);
    collect(t3, c);
    collect(t4, c);
    collect(t5, c);
    collect(t6, c);
}

void collect(Tree t1, Tree t2, Tree t3, Tree t4, Tree t5, Tree t6, Tree t7, Collector c){
    collect(t1, c);
    collect(t2, c);
    collect(t3, c);
    collect(t4, c);
    collect(t5, c);
    collect(t6, c);
    collect(t7, c);
}

void collect(Tree t1, Tree t2, Tree t3, Tree t4, Tree t5, Tree t6, Tree t7, Tree t8, Collector c){
    collect(t1, c);
    collect(t2, c);
    collect(t3, c);
    collect(t4, c);
    collect(t5, c);
    collect(t6, c);
    collect(t7, c);
    collect(t8, c);
}

void collect(Tree t1, Tree t2, Tree t3, Tree t4, Tree t5, Tree t6, Tree t7, Tree t8, Tree t9, Collector c){
    collect(t1, c);
    collect(t2, c);
    collect(t3, c);
    collect(t4, c);
    collect(t5, c);
    collect(t6, c);
    collect(t7, c);
    collect(t8, c);
    collect(t9, c);
}

void collect(list[Tree] currentTrees, Collector c){
    n = size(currentTrees);
    i = 0;
    while(i < n){
        collect(currentTrees[i], c);
        i += 1;
    }
}

// ---- default collector -----------------------------------------------------

void collectArgs1(list[Tree] args, Collector c){
    //println("args1:<for(a <- args){>|<a>|<}>");
    int n = size(args);
    int i = 0;
    while(i < n){
        collect(args[i], c);
        i += 1;
    }
}

void collectArgs2(list[Tree] args, Collector c){
    //println("args2:<for(a <- args){>|<a>|<}>");
    int n = size(args);
    int i = 0;
    while(i < n){
        collect(args[i], c);
        i += 2;
    }
}

void collectArgsN(list[Tree] args, int delta, Collector c){
    //println("argsN:<for(a <- args){>|<a>|<}>");
    int n = size(args);
    int i = 0;
    while(i < n){
        collect(args[i], c);
        i += delta;
    }
}

set[str] ignored = {"lit", "cilit", "char-class"};

bool allSymbolsIgnored(list[Symbol] symbols){
    n = size(symbols);
    int i = 0;
    while(i < n){
        if(getName(symbols[i]) notin ignored) return false;
        i += 1;
    }
    return true;
}

str treeAsMessage(Tree t, int charLimit=120) {
    str msg = "" + "<t>"; // workaround funny ambiguity

    // limit the string length and show visually with ...
    if (size(msg) > charLimit) {
        msg = "<msg[0..charLimit]>...";
    }

    // replace newlines by spaces
    msg = visit (msg) {
        case /\r\n/ => " "
        case /\n/ => " "
    };

    return msg;
}

default void collect(Tree currentTree, Collector c){
    if(currentTree has prod){
        switch(getName(currentTree.prod.def)){
        case "label":
            { p = currentTree.prod; collect(appl(prod(p.def.symbol, p.symbols, p.attributes/*, src=getLoc(currentTree)*/), currentTree.args), c); }
        case "start":
            { p = currentTree.prod; collect(appl(prod(p.def.symbol, p.symbols, p.attributes/*, src=getLoc(currentTree)*/), currentTree.args), c); }
        case "sort":
            { args = currentTree.args;
              nargs = size(args);
              if(nargs == 1) collectArgs2(args, c); // automatic treatment of chain rules
              else if(nargs > 0) {
                  c.report(info(currentTree, "Missing `collect` for %q", treeAsMessage(currentTree)));
                  collectArgs2(args, c);
                 //was: throw TypePalUsage("Missing `collect` for <currentTree.prod>", [getLoc(currentTree)]);
              }
            }
        case "parameterized-sort":
            { args = currentTree.args;
              nargs = size(args);
                             // Hack to circumvent improper handling of parameterized sorts in interpreter
              if(nargs == 1 || currentTree.prod.def.name in { "Mapping", "KeywordArgument", "KeywordArguments"}) collectArgs2(args, c);
              else if(nargs > 0) {
                c.report(info(currentTree, "Missing `collect` for %q", treeAsMessage(currentTree)));
                collectArgs2(args, c);
                //was: throw TypePalUsage("Missing `collect` for <currentTree.prod>", [getLoc(currentTree)]);
              }
            }
       case "lex":
            { p = currentTree.prod;
              if(!allSymbolsIgnored(p.symbols)){
                args = currentTree.args;
                nargs = size(args);
                collectArgsN(args, 1, c);
                //if(nargs == 1 || p.def.name in {"DecimalIntegerLiteral"}) collectArgs1(args, c);
                //else if(nargs > 0) {
                //    throw TypePalUsage("Missing `collect` for <p>: `<currentTree>`");
                //}
              }
            }
        case "parameterized-lex":
            { p = currentTree.prod;
              if(!allSymbolsIgnored(p.symbols)){
                args = currentTree.args;
                nargs = size(args);
                if(nargs == 1) collectArgs1(args, c);
                else if(nargs > 0) {
                     c.report(info(currentTree, "Missing `collect` for %q", treeAsMessage(currentTree)));
                    collectArgs2(args, c);
                    // was throw TypePalUsage("Missing `collect` for <currentTree.prod>", [getLoc(currentTree)]);
                }
              }
            }
       case "conditional":
            { p = currentTree.prod; collect(appl(prod(p.def.symbol, p.symbols, p.attributes), currentTree.args), c); }
        case "iter":
            if(getName(currentTree.prod.def.symbol) == "lex")  collectArgs1(currentTree.args, c); else collectArgs2(currentTree.args, c);
        case "iter-star":
            if(getName(currentTree.prod.def.symbol) == "lex")  collectArgs1(currentTree.args, c); else collectArgs2(currentTree.args, c);
        case "iter-seps":
            collectArgsN(currentTree.args, 1 + size(currentTree.prod.def.separators), c);
        case "iter-star-seps":
            collectArgsN(currentTree.args, 1 + size(currentTree.prod.def.separators), c);
        case "seq":
            collectArgs2(currentTree.args, c);
        case "alt":
            collectArgs2(currentTree.args, c);
        case "opt":
            collectArgs2(currentTree.args, c);
        //case "lit":;

        //default: { println("COLLECT, default: <getName(currentTree.prod.def)>: <currentTree>");  }

        // Just skip the cases "lit", "layouts": ;

        }
      }
   }