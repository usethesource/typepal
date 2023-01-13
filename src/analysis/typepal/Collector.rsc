@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::Collector
 
import Node;
import Map;
import ParseTree;
import Set;
import Relation;
import IO;
import Type;
import Location;

import analysis::typepal::Version;

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

bool isTypeVarFree(AType t)
    =  !(/tvar(loc _) := t);

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
    println("<indent>requ `<rname>` for <dependsOn[0]>");
    if(full) printDeps(dependsOn, indent, facts);
}
void print(reqComparable(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0]>");
    if(full) printDeps(dependsOn, indent, facts);
}

void print(reqSubtype(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0]>");
    if(full) printDeps(dependsOn, indent, facts);
}

void print(reqUnify(str rname, value l, value r, list[loc] dependsOn, FailMessage fm), str indent, map[loc,AType] facts, bool full=true){
    println("<indent>requ `<rname>` for <dependsOn[0]>");
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
    | calcLub(str cnname, list[loc] srcs, list[loc] dependsOn, list[AType(Solver s)] getATypes, bool eager=false)
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

anno loc Tree@src;

Collector newCollector(str modelName, map[str,Tree] namedTrees, TypePalConfig config){
    
    str normalizeName(str input) {  
            return config.normalizeName(input); 
         }
    loc globalScope = |global-scope:///|;
    Defines defines = {};
    
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
    
    void _define(str orgId, IdRole idRole, value def, DefInfo info){
        if(building){
            loc l = |undefined:///|;
            if(Tree tdef := def) l = getLoc(tdef);
            else if(loc ldef := def) l = ldef;
            else throw TypePalUsage("Argument `def` of `define` should be `Tree` or `loc`, found <typeOf(def)>");
            
            uid = normalizeName(orgId);
           
            // println("define: <id>, <idRole>, <def>");
            //println("definesPerLubScope[currentLubScope]: <definesPerLubScope[currentLubScope]>");
            
            if(info is defTypeLub){  
                // Look for an outer variable declaration of id that overrules the defTypeLub   
                for(Define def <- defines + definesPerLubScope[currentLubScope]){
                    if(def.id == uid && config.isInferrable(def.idRole)){
                        if(def.scope in scopeStack<0>) {
                            uses += use(uid, orgId, l, currentScope, {def.idRole});
                            return;
                        }
                    }
                }
                lubDefinesPerLubScope[currentLubScope] += <currentScope, uid, orgId, idRole, l, info>;
            } else {
                //println("define: add to definesPerLubScope[<currentLubScope>]: <<currentScope, id, idRole, l, info>>");
                definesPerLubScope[currentLubScope] += <currentScope, uid, orgId, idRole, l, info>; 
            }
        } else {
            throw TypePalUsage("Cannot call `define` on Collector after `run`");
        }
    }
    
    Tree _predefine(str id, IdRole idRole, value def, DefInfo info){
        l = _getPredefinedTree(def, id);
        _define(id, idRole, l, info);
        return l;
    }
    
    Tree _predefineInScope(value scope, str id, IdRole idRole, DefInfo info){
        l = _getPredefinedTree(scope, id);
        
        _defineInScope(scope, id, idRole, l, info);
        return l;
    }

    Tree _getPredefinedTree(value scope, str id){
    
        loc defining = |undefined:///|;
        if(Tree tdef := scope) defining = getLoc(tdef);
        else if(loc ldef := scope) defining = ldef;
        else throw TypePalUsage("Argument `scope` should be `Tree` or `loc`, found <typeOf(scope)>");
    
        nPredefinedTree += 1;
        return appl(prod(sort("$PREDEFINED-<id>"), [], {}),
                    [])[@\src=defining[query="predefined=<id>"][fragment="<nPredefinedTree>"]];
    }
    
    bool _isAlreadyDefined(str id,  Tree useOrDef){
        lubdefs = { def | def <- lubDefinesPerLubScope[currentLubScope], def.id == id };
        
        if(!isEmpty(lubdefs) && any(def <- lubdefs, isContainedIn(getLoc(useOrDef), def.scope))){
            return true;
        }
        
        for(def <- defines, def.id == id, config.isInferrable(def.idRole), isContainedIn(getLoc(useOrDef), def.scope)){
            return true;
        }
        return false;
    }
        
    void _defineInScope(value scope, str orgId, IdRole idRole, value def, DefInfo info){
        if(building){
            loc definingScope = |undefined:///|;
            if(Tree tscope := scope) definingScope = getLoc(tscope);
            else if(loc lscope := scope) definingScope = lscope;
            else throw TypePalUsage("Argument `scope` of `defineInScope` should be `Tree` or `loc`, found <typeOf(scope)>");
            
            loc l = |undefined:///|;
            if(Tree tdef := def) l = getLoc(tdef);
            else if(loc ldef := def) l = ldef;
            else throw TypePalUsage("Argument `def` of `defineInScope` should be `Tree` or `loc`, found <typeOf(def)>");
            
            uid = normalizeName(orgId);
            if(info is defTypeLub){
                throw TypePalUsage("`defLub` cannot be used in combination with `defineInScope`");
            } else {
                defines += <definingScope, uid, orgId, idRole, l, info>;
            }
        } else {
            throw TypePalUsage("Cannot call `defineInScope` on Collector after `run`");
        }
    }
   
    void _use(Tree occ, set[IdRole] idRoles) {
        if(building){            
           //println("use <occ> at <getLoc(occ)> in scope <currentScope>");
           orgId = "<occ>";
           uses += use(normalizeName(orgId), orgId, getLoc(occ), currentScope, idRoles);
        } else {
            throw TypePalUsage("Cannot call `use` on Collector after `run`");
        }
    }
    
    void _useLub(Tree occ, set[IdRole] idRoles) {
        if(building){
           //println("useLub <occ> at <getLoc(occ)> in scope <currentScope>");
           lubUsesPerLubScope[currentLubScope] += <normalizeName("<occ>"), "<occ>", currentScope, idRoles, getLoc(occ)>;
        } else {
            throw TypePalUsage("Cannot call `useLub` on Collector after `run`");
        }
    }
    
    void _addPathToDef(Tree occ, set[IdRole] idRoles, PathRole pathRole) {
        if(building){
            orgId = "<occ>";
            u = use(normalizeName(orgId), orgId, getLoc(occ), currentScope, idRoles);
            uses += u;
            referPaths += referToDef(u, pathRole);
        } else {
            throw TypePalUsage("Cannot call `_addPathToDef` on Collector after `run`");
        }
    }
    
    AType(Solver) makeGetTypeInType(Tree container, Tree selector, set[IdRole] idRolesSel, loc scope){
        return AType(Solver s) { 
            return s.getTypeInType(s.getType(container), selector, idRolesSel, scope);
         };
    }
    
    void _useViaType(Tree container, Tree selector, set[IdRole] idRolesSel){
        if(building){
            name = normalizeName("<selector>");
            sloc = getLoc(selector);
            calculators += calc("useViaType `<name>` in <getLoc(container)>", sloc,  [getLoc(container)],  makeGetTypeInType(container, selector, idRolesSel, currentScope));
        } else {
            throw TypePalUsage("Cannot call `useViaType` on Collector after `run`");
        }
    }
   
    void _useQualified(list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles){
        if(building){
           uses += useq([normalizeName(id) | id <- ids], "<occ>", getLoc(occ), currentScope, idRoles, qualifierRoles);
        } else {
            throw TypePalUsage("Cannot call `useQualified` on Collector after `run`");
        }  
     }
     
     void _addPathToQualifiedDef(list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathRole pathRole){
        if(building){
            u = useq([normalizeName(id) | id <- ids], "<occ>", getLoc(occ), currentScope, idRoles, qualifierRoles);
            uses += u;
            referPaths += referToDef(u, pathRole);
        } else {
            throw TypePalUsage("Cannot call `addPathToQualifiedDef` on Collector after `run`");
        } 
    }
    
    void _addPathToType(Tree occ, PathRole pathRole){
         if(building){
            referPaths += referToType(getLoc(occ), currentScope, pathRole);
        } else {
            throw TypePalUsage("Cannot call `addPathToType` on Collector after `run`");
        } 
    }
    
    void _enterScope(Tree inner){
        enterScope(getLoc(inner));
    }
    
    void _enterCompositeScope(list[Tree] trees){
        enterScope(cover([getLoc(t) | t <- trees]));
    }
    
    void _enterLubScope(Tree inner){
        enterScope(getLoc(inner), lubScope=true);
    }
    
    void _enterCompositeLubScope(list[Tree] trees){
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
    
    void _leaveScope(Tree inner){
        leaveScope(getLoc(inner));
    }
    
    void _leaveCompositeScope(list[Tree] trees){
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
                //println("LEAVE LUBSCOPE <inner>"); 
                //println("lubDefinesPerLubScope before");
                //iprintln(lubDefinesPerLubScope);
                
                extraDefs = finalizeDefines(currentLubScope);
                defines += extraDefs;
                //println("LEAVESCOPE, extraDefs"); iprintln(extraDefs);
                //println("LEAVESCOPE, lubDefinesPerLubScope after");
                //iprintln(lubDefinesPerLubScope);
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
    
    void _setScopeInfo(loc scope, ScopeRole scopeRole, value scopeInfo){
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
    
    lrel[loc scope, value scopeInfo] _getScopeInfo(ScopeRole scopeRole){
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
    
    loc _getScope(){
        if(building){
           //if(currentScope == globalScope) throw TypePalUsage("`getScope` requires a user-defined scope; missing `enterScope`");
            return currentScope;
        } else {
            throw TypePalUsage("Cannot call `getScope` on Collector after `run`");
        }
    }
   
    void _require(str name, Tree src, list[value] dependencies, void(Solver s) preds){ 
        if(building){
           requirements += req(name, getLoc(src), dependenciesAslocList(dependencies), preds);
        } else {
            throw TypePalUsage("Cannot call `require` on Collector after `run`");
        }
    } 
    
    void _requireEager(str name, Tree src, list[value] dependencies, void(Solver s) preds){ 
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
   
    void _requireEqual(value l, value r, FailMessage fm){
        if(building){
           requirements += reqEqual("`<l>` requireEqual `<r>`", getLocIfTree(l), getLocIfTree(r), getDeps(l, r), fm);
        } else {
            throw TypePalUsage("Cannot call `requireEqual` on Collector after `run`");
        }
    }
    
    void _requireComparable(value l, value r, FailMessage fm){
        if(building){
           requirements += reqComparable("`<l>` requireEqual `<r>`", getLocIfTree(l), getLocIfTree(r), getDeps(l, r), fm);
        } else {
            throw TypePalUsage("Cannot call `requireComparable` on Collector after `run`");
        }
    }
    
    void _requireSubType(value l, value r, FailMessage fm){
        if(building){
           requirements += reqSubtype("`<l>` requireSubType `<r>`", getLocIfTree(l), getLocIfTree(r), getDeps(l, r), fm);
        } else {
            throw TypePalUsage("Cannot call `requireSubType` on Collector after `run`");
        }
    }
    
    void _requireUnify(value l, value r, FailMessage fm){
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
    
     void _fact(Tree tree, value tp){  
        if(building){
          srcLoc = getLoc(tree);
          if(AType atype := tp){
            if(isTypeVarFree(atype)) {
                if(facts[srcLoc]? && !isValidReplacement(facts[srcLoc], atype)){
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
                if(facts[fromLoc]?){
                    fromType = facts[fromLoc];
                    if(facts[srcLoc]? && !isValidReplacement(facts[srcLoc], fromType)){
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
    
    AType _getType(Tree tree){
        if(building){
            srcLoc = getLoc(tree);
            if(facts[srcLoc]?) return facts[srcLoc];
            //println("Collector.getType: <srcLoc>");
            throw TypeUnavailable();
        } else {
            throw TypePalUsage("Cannot call `getType` on Collector after `run`");
        }
    }
    
    void _calculate(str name, Tree src, list[value] dependencies, AType(Solver s) calculator){
        if(building){
           srcLoc = getLoc(src);
           calculators += calc(name, srcLoc, dependenciesAslocList(dependencies) - srcLoc, calculator);
        } else {
            throw TypePalUsage("Cannot call `calculate` on Collector after `run`");
        }
    }
    
    void _calculateEager(str name, Tree src, list[value] dependencies, AType(Solver s) calculator){
        if(building){
           srcLoc = getLoc(src);
           calculators += calc(name, srcLoc, dependenciesAslocList(dependencies) - srcLoc, calculator, eager=true);
        } else {
            throw TypePalUsage("Cannot call `calculateEager` on Collector after `run`");
        }
    }
    
    bool _report(FailMessage fm){
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
    
     bool _reports(list[FailMessage] fms){
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
    
    AType _newTypeVar(value src){
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
    
    void _push(str key, value val){
        if(storeVals[key]? && list[value] old := storeVals[key]){
           storeVals[key] = val + old;
        } else {
           storeVals[key] = [val];
        }
    }
    
    value _pop(str key){
        if(storeVals[key]? && list[value] old := storeVals[key], size(old) > 0){
           pval = old[0];
           storeVals[key] = tail(old);
           return pval;
        } else {
           throw TypePalUsage("Cannot pop from empty stack for key `<key>`");
        }
    }
    
    value _top(str key){
        if(storeVals[key]? && list[value] old := storeVals[key], size(old) > 0){
           return old[0];
        } else {
           throw TypePalUsage("Cannot get top from empty stack for key `<key>`");
        }
    }
    
    list[value] _getStack(str key){
        if(storeVals[key]? && list[value] old := storeVals[key]){
            return old;
        }
        return [];
    }
    
    void _clearStack(str key){
        storeVals[key] = [];
    }
    
    TypePalConfig _getConfig(){
        return config;
    }
    
    void _setConfig(TypePalConfig cfg){
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
        //println("existsFixedDefineInOuterScope: <id>, <lubScope>");
        outer = lubScope;
        while(scopes[outer]? && scopes[outer] != |global-scope:///|){
            outer = scopes[outer];
            //println("outer: <outer>");
            //println("definesPerLubScope[outer] ? {}: <definesPerLubScope[outer] ? {}>");
            for(<loc _, id, _, idRole , loc _, DefInfo _> <- definesPerLubScope[outer] ? {}, config.isInferrable(idRole)){
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
       // println("finalizeDefines: <lubScope>, <definesPerLubScope[lubScope]>");
        set[Define] extra_defines = {};
       
        rel[loc,loc] enclosedScopes = scopesPerLubScope[lubScope]* + <lubScope,lubScope>;
        set[loc] allScopes = carrier(enclosedScopes);
        
        set[Define] deflubs_in_lubscope = lubDefinesPerLubScope[lubScope];
        set[str] deflub_names = deflubs_in_lubscope<1>;
        rel[str id, str orgId, loc idScope, set[IdRole] idRoles, loc occ] uselubs_in_lubscope = lubUsesPerLubScope[lubScope];  
         
        
        set[Define] local_fixed_defines = definesPerLubScope[lubScope]; //{ def | def <- definesPerLubScope[lubScope], config.isInferrable(def.idRole) };
        extra_defines += definesPerLubScope[lubScope];
        //extra_defines += local_fixed_defines;
        
        rel[str, loc] local_fixed_defines_scope = local_fixed_defines<1,0>;
        set[str] ids_with_fixed_def = domain(local_fixed_defines_scope);
        
        for(str id <- deflub_names){
            set[loc] id_defined_in_scopes = { def.scope | def <- deflubs_in_lubscope, def.id == id };
            set[Use] id_used_in_scopes = {use(tup.tid, tup.orgId, tup.occ, tup.idScope, tup.idRoles) | tuple[str tid, str orgId, loc idScope, set[IdRole] idRoles, loc occ] tup <- uselubs_in_lubscope, tup.tid == id};
            id_defined_in_scopes = { sc1 | loc sc1 <- id_defined_in_scopes, isEmpty(enclosedScopes) || !any(loc sc2 <- id_defined_in_scopes, sc1 != sc2, <sc2, sc1> in enclosedScopes)};
            
            //println("Consider <id>, defined in scopes <id_defined_in_scopes>");
            //println("local_fixed_defines: <local_fixed_defines>");
            //println("local_fixed_defines[lubScope, id]: <local_fixed_defines[lubScope, id]>");
            
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
    
    void _addTModel(TModel tm){
        if(!isValidVersion(tm.version)){
            throw TypePalUsage("TModel for <tm.modelName> uses TPL version <tm.version>, but <getCurrentTplVersion()> is required");
        }
        messages += tm.messages;
        //overlapping_scopes = domain(scopes) & domain(tm.scopes);
        //if(!isEmpty(overlapping_scopes)) {
        //    for(s <- overlapping_scopes){
        //        if(scopes[s] != tm.scopes[s]){
        //            println("current model:"); iprintln(domain(scopes));
        //            println("added model:"); iprintln(domain(tm.scopes));
        //            throw "overlapping scopes for <overlapping_scopes>";
        //        }
        //     }
        //}
        scopes += tm.scopes;
        
        // Temporary conversion step needed for bootstrap (new tuple element orgId has been added)
        // TODO: remove after next iteration
        
        //tm = visit(tm){ case [value]<loc scope, str id, IdRole idRole, loc defined, DefInfo defInfo> => <scope, id, id, idRole, defined, defInfo> };
  
        defines += tm.defines;
        
        //overlapping_facts = domain(facts) & domain(tm.facts);
        //if(!isEmpty(overlapping_facts)) {
        //     for(s <- overlapping_facts){
        //        if(facts[s] != tm.facts[s]){
        //            println("current model:"); iprintln(domain(scopes));
        //            println("added model:"); iprintln(domain(tm.scopes));
        //            throw "incompatible fact for <s>: <facts[s]> != <tm.facts[s]>";
        //        }
        //     }
        //}
        facts += tm.facts;
        paths += tm.paths;
    }
    
    TModel _run(){
        if(building){
           building = false;
           
           if(size(scopeStack) == 0){
                throw TypePalUsage("Bottom entry missing from scopeStack: more leaveScopes than enterScopes");
           }
           
           if(size(scopeStack) > 1){
                unclosed = [scope | <loc scope, bool _, map[ScopeRole, value] _> <- scopeStack];
                throw TypePalUsage("Missing `leaveScope`(s): unclosed scopes <unclosed>");
           }
           
           tm = tmodel();
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
           
           tm.calculators = calculators;
           tm.requirements = requirements;  
           tm.store = storeVals;        storeVals = ();
           tm.definitions = ( def.defined : def | Define def <- defines);
           map[loc, map[str, rel[IdRole idRole, loc defined]]] definesMap = ();
           for(<loc scope, str id, str _orgId, IdRole idRole, loc defined, DefInfo _> <- defines){
                map[str, rel[IdRole idRole, loc defined]] dm = ();
                if(definesMap[scope]?) dm = definesMap[scope];
                dm[id] =  (dm[id] ? {}) + {<idRole, defined>};
                definesMap[scope] = dm;
           }
           //for(<loc scope, str id, IdRole idRole, loc defined, DefInfo defInfo> <- defines){
           //     definesMap[<scope, id>] = definesMap[<scope, id>]? ?  definesMap[<scope, id>] + {<idRole, defined>} : {<idRole, defined>};
           //}
           tm.definesMap = definesMap;
           defines = {};
           tm.messages = messages;
           //return resolvePath(tm); 
           return tm;
        } else {
           throw TypePalUsage("Cannot call `run` on Collector after `run`");
        }
    }
        
    return collector(
        /* Life cycle */    _run,
        
        /* Configure */     _getConfig,
                            _setConfig,
                            
        /* Scoping */       _enterScope, 
                            _enterCompositeScope,
                            _enterLubScope,
                            _enterCompositeLubScope,
                            _leaveScope,
                            _leaveCompositeScope,
                            _getScope,
                            
        /* Scope Info */    _setScopeInfo,
                            _getScopeInfo,
                            
        /* Nested Info */   _push,
                            _pop,
                            _top,
                            _getStack,
                            _clearStack,
                            
        /* Compose */       _addTModel,
        
        /* Reporting */     _report, 
                            _reports,
                            
        /* Define */        _define,
                            _defineInScope,
                            _predefine,
                            _predefineInScope,
                            _isAlreadyDefined,
                            
        /* Use */           _use, 
                            _useQualified, 
                            _useViaType,
                            _useLub,
                            
        /* Path */          _addPathToDef,
                            _addPathToQualifiedDef,
                            _addPathToType,
                           
        /* Inference */     _newTypeVar,  
                
        /* Fact */          _fact,
        
        /* GetType */       _getType,
        
        /* Calculate */     _calculate, 
                            _calculateEager,
                            
        /* Require */       _require, 
                            _requireEager,
                            _requireEqual,
                            _requireComparable,
                            _requireSubType,
                            _requireUnify
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
str getLine(Tree t){
    if(!t@\loc?) return "?";
    l = t@\loc;
    if(l.begin?) return "<l.begin.line>";
    return "?";
}
default void collect(Tree currentTree, Collector c){
    //println("<getLine(currentTree)>|<currentTree>|");
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
                 throw TypePalUsage("Missing `collect` for <currentTree.prod>", [getLoc(currentTree)]); 
              }
            }
        case "parameterized-sort":
            { args = currentTree.args;
              nargs = size(args);
                             // Hack to circumvent improper handling of parameterized sorts in interpreter
              if(nargs == 1 || currentTree.prod.def.name in { "Mapping", "KeywordArgument", "KeywordArguments"}) collectArgs2(args, c); 
              else if(nargs > 0) { 
                throw TypePalUsage("Missing `collect` for <currentTree.prod>", [getLoc(currentTree)]);
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
                    throw TypePalUsage("Missing `collect` for <currentTree.prod>", [getLoc(currentTree)]); 
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