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
import String;
import Set;
import Relation;
import util::Benchmark;
import IO;

extend analysis::typepal::ScopeGraph;
extend analysis::typepal::AType;

import  analysis::typepal::Messenger;
import analysis::typepal::FailMessage;

import analysis::typepal::TypePalConfig;
import analysis::typepal::TypePal;
import analysis::typepal::Utils;

// Extract (nested) tree locations and type variables from a list of dependencies
list[loc] dependenciesAslocList(list[value] dependencies){
    return 
        for(d <- dependencies){
            if(Tree t := d){
                append getLoc(t);
            } else if(tvar(tv) := d){
                append tv;
            } else {
                throw TypePalUsage("Dependency should be a tree or type variable, found <d>");
            }
        };
} 

set[loc] dependenciesAslocs(list[Tree] dependencies)
    = toSet(dependenciesAslocList(dependencies));

// Definition info used during type checking
data DefInfo
    = defType(AType atype) 
    | defGetType(Tree item)                                                   // Explicitly given AType
    | defType(set[loc] dependsOn, AType(Solver s) getAType)                           // AType given as callback.
 //   | defLub(list[AType] atypes)                                              // redefine previous definition
    | defLub(set[loc] dependsOn, set[loc] defines, list[AType(Solver s)] getATypes)   // redefine previous definition
    ;

DefInfo defType(list[Tree] dependsOn, AType(Solver s) getAType){
    return defType(dependenciesAslocs(dependsOn), getAType);
 }
    
DefInfo defLub(list[Tree] dependsOn, AType(Solver s) getAType)
    = defLub(dependenciesAslocs(dependsOn), {}, [getAType]);


// The basic ingredients for type checking: facts, requirements and overloads

// Facts about location src, given dependencies and an AType callback
data Fact
    = openFact(loc src, AType uninstantiated)
    | openFact(loc src, set[loc] dependsOn, AType(Solver s) getAType)
    | openFact(set[loc] srcs, set[loc] dependsOn, list[AType(Solver s)] getATypes)
    ;

// A named requirement for location src, given dependencies and a callback predicate
// Eager requirements are tried when not all dependencies are known.
data Requirement
    = openReq(str rname, loc src, loc scope, list[loc] dependsOn, bool eager, void(Solver s) preds);

// Named type calculator for location src, given args, and resolve callback 
// Eager calculators are tried when not all dependencies are known.   
data Calculator
    = calculate(str cname, loc scope, loc src, list[loc] dependsOn, bool eager, AType(Solver s) calculator);

// The basic Fact & Requirement Model; can be extended in specific type checkers
data TModel (
        map[loc,Calculator] calculators = (),
        map[loc,AType] facts = (), 
        set[Fact] openFacts = {},
        set[Requirement] openReqs = {},
        map[AType, loc] namedTypes = (),
        Uses indirectUses = [],
 //       map[loc,loc] tvScopes = (),
        list[Message] messages = [],
        map[str,value] store = (),
        map[loc, Define] definitions = (),
        TypePalConfig config = tconfig()
        );

void printTModel(TModel tm){
    println("TModel(");
    println("  defines = {");
    for(Define d <- tm.defines){
        println("    \<<d.scope>, <d.id>, <d.idRole>, <d.defined>\>"); 
    }
    println("  },");
    println("  scopes = (");
    for(loc inner <- tm.scopes){
        println("    <inner>: <tm.scopes[inner]>");
    }
    println("  ),");
    println("  paths = {");
    for(<loc from, PathRole pathRole, loc to> <- tm.paths){
        println("    \<<from>, <pathRole>, <to>\>");
    }
    println("  },");
    println("  referPath = {");
    for(c <- tm.referPaths){
        println("    <c>");
    }
    println("  },");

    //iprintln(tm.uses);
    println("  uses = [");
    for(Use u <- tm.uses){
        println("    use(<u.ids? ? u.ids : u.id>, <u.occ>, <u.scope>, <u.idRoles>, <u.qualifierRoles? ? u.qualifierRoles : "">)");
    }
    println("  ]");
    println(");");
}

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
    for(t <- currentTrees) collect(t, c);
}

// Default definition for collect; to be overridden in a specific type checker
// for handling syntax-constructs-of-interest
default void collect(Tree currentTree, Collector c){
   //println("default collect: <typeOf(currentTree)>: <currentTree>");
   if(nlexical == 0)  collectParts(currentTree, c); else collectLexicalParts(currentTree, c); 
}

private  set[str] skipSymbols = {"lex", "layouts", "keywords", "lit", "cilit", "char-class"};

int delta = 2;
void collectParts(Tree currentTree, Collector c){
   //println("collectParts: <typeOf(currentTree)>: <currentTree>");
   if(currentTree has prod /*&& getName(currentTree.prod.def) notin skipSymbols*/){
       args = currentTree.args;
       int n = size(args);
       int i = 0;
       while(i < n){
        collect(args[i], c);
        i += delta;
       }
   } 
   //else {
   // println("collectParts, skipping: <typeOf(currentTree)>: <currentTree>");
   //}
}

int nlexical = 0;

void collectLexical(Tree currentTree, Collector c){
    //println("collectLexical: <typeOf(currentTree)>: <currentTree>");
    nlexical += 1;
    collect(currentTree, c);
    collectLexicalParts(currentTree, c);
    nlexical -= 1;
}

void collectLexicalParts(Tree currentTree, Collector c){
   //println("collectLexicalParts: <typeOf(currentTree)>: <currentTree>"); 
   delta =1 ;
   if(currentTree has prod /*&& getName(currentTree.prod.def) notin skipSymbols*/){
       args = currentTree.args;
       int n = size(args);
       int i = 0;
       while(i < n){
        collectLexical(args[i], c);
        i += 1;
       }
   }
   delta = 2;
}

tuple[bool, loc] findMostRecentDef(set[loc] defs){
    d2l = (def.fragment : def | loc def <- defs);
    strippedDefs = {def[fragment=""][offset=0][length=0][begin=<0,0>][end=<0,0>] | def <- defs};
    if({sdef} := strippedDefs){
        def = d2l[sort([d.fragment | loc d <- defs])[-1]];
        println("findMostRecentDef: <defs> ==\> \<true, <def>\>");
        return <true, def>;
    }
    //println("findMostRecentDef: <defs> ==\> \<false, |unknown:///|\>");
    return <false, |unknown:///|>;
}
    
data Collector 
    = collector(
        void (str id, IdRole idRole, value def, DefInfo info) define,
        void (value scope, str id, IdRole idRole, value def, DefInfo info) defineInScope,
        void (Tree occ, set[IdRole] idRoles) use,
        void (Tree occ, set[IdRole] idRoles) useLub,
        void (Tree occ, set[IdRole] idRoles, PathRole pathRole) useViaPath,
        void (Tree container, set[IdRole] idRolesCont, Tree selector, set[IdRole] idRolesSel) useViaNamedType,
        void (list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles) useQualified,
        void (list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathRole pathRole) useQualifiedViaPath,   
        void (Tree inner) enterScope,
        void (Tree inner) enterLubScope,
        void (Tree inner) leaveScope,
        void (loc scope, ScopeRole scopeRole, value info) setScopeInfo,
        lrel[loc scope, value scopeInfo] (ScopeRole scopeRole) getScopeInfo,
        loc () getScope,
       
        void (str name, Tree src, list[value] dependencies, void(Solver s) preds) require,
        void (str name, Tree src, list[value] dependencies, void(Solver s) preds) requireEager,
        void (Tree src, AType tp) fact,
        void (str name, Tree src, list[value] dependencies, AType(Solver s) calculator) calculate,
        void (str name, Tree src, list[value] dependencies, AType(Solver s) calculator) calculateEager,
        void (Tree target, Tree src) sameType,
        bool (FailMessage ) report,
        bool (set[FailMessage] msgs) reports,
        AType (Tree src) newTypeVar,
        void(str key, value val) push,
        value (str key) pop,
        value (str key) top,
        list[value] (str key) getStack,
        void (str key) clearStack,
        void (TModel tm) addTModel,
        TypePalConfig () getConfig,
        void (TypePalConfig cfg) setConfig,
        TModel () run
      ); 

AType(Solver s) makeClos1(AType tp) = AType (Solver s){ return tp; };                   // TODO: workaround for compiler glitch
void(Solver s) makeClosError(Message msg) = void(Solver s){ throw  checkFailed({msg}); };
void(Solver s) makeClosErrors(set[Message] msgs) = void(Solver s){ throw checkFailed(msgs); };
             
Collector defaultCollector(Tree t) = newCollector(t);    
 
alias LubDefine = tuple[loc lubScope, str id, loc scope, IdRole idRole, loc defined, DefInfo defInfo]; 
alias LubDefine2 = tuple[str id, loc scope, IdRole idRole, loc defined, DefInfo defInfo];       

Collector newCollector(Tree t, TypePalConfig config = tconfig(), bool debug = false){
    configScopeGraph(config);
    
    unescapeName = config.unescapeName;
    loc rootLoc = getLoc(t).top;
    loc globalScope = |global-scope:///|;
    Defines defines = {};
    
    map[loc, set[Define]] definesPerLubScope = (globalScope: {});
    map[loc, set[LubDefine2]] lubDefinesPerLubScope = (globalScope: {});
    map[loc, rel[str id, loc idScope, set[IdRole] idRoles, loc occ]] lubUsesPerLubScope = (globalScope: {});
    map[loc, rel[loc,loc]]  scopesPerLubScope = (globalScope: {});
 
    Scopes scopes = ();
    
    Paths paths = {};
    set[ReferPath] referPaths = {};
    map[AType,loc] namedTypes = ();
    Uses uses = [];
    Uses indirectUses = [];
    map[str,value] storeVals = ();
    
    map[loc,Calculator] calculators = ();
    map[loc,AType] facts = ();
    set[Fact] openFacts = {};
    set[Requirement] openReqs = {};
    int ntypevar = -1;
    list[Message] messages = [];
   
    loc currentScope = globalScope; //getLoc(t);
    loc rootScope = globalScope; //currentScope;
  
    scopes[getLoc(t)] = globalScope;
    lrel[loc scope, bool lubScope, map[ScopeRole, value] scopeInfo] scopeStack = [<globalScope, false, (anonymousScope(): false)>];
    list[loc] lubScopeStack = [];
    loc currentLubScope = globalScope;
    
    bool building = true;
    
    void _define(str id, IdRole idRole, value def, DefInfo info){
        if(building){
            loc l;
            if(Tree tdef := def) l = getLoc(tdef);
            else if(loc ldef := def) l = ldef;
            else throw TypePalUsage("Argument `def` of `define` should be `Tree` or `loc`, found <typeOf(def)>");
            
            id = unescapeName(id);
            //println("definesPerLubScope[currentLubScope]: <definesPerLubScope[currentLubScope]>");
            
            if(info is defLub /*&& isEmpty(definesPerLubScope[currentLubScope][currentScope, id])*/){
                //if(id=="ddd")println("defLub: <currentLubScope>, <{<id, currentScope, idRole, l, info>}>");           
                lubDefinesPerLubScope[currentLubScope] += {<id, currentScope, idRole, l, info>};
            } else {
                //println("define: <<currentScope, id, idRole, l, info>>");
                definesPerLubScope[currentLubScope] += <currentScope, id, idRole, l, info>;
            }
        } else {
            throw TypePalUsage("Cannot call `define` on Collector after `run`");
        }
    }
     
    AType(Solver) makeDefineNamedTypeCalculator(loc l, AType(Solver) getAType){
        return AType(Solver s) { println("makeDefineNamedTypeCalculator");
         AType t = getAType(s); s.addNamedType(t, l); return t; };
    }
    
    void _defineInScope(value scope, str id, IdRole idRole, value def, DefInfo info){
        if(building){
            loc definingScope;
            if(Tree tscope := scope) definingScope = getLoc(tscope);
            else if(loc lscope := scope) definingScope = lscope;
            else throw TypePalUsage("Argument `scope` of `defineInScope` should be `Tree` or `loc`, found <typeOf(scope)>");
            
            loc l;
            if(Tree tdef := def) l = getLoc(tdef);
            else if(loc ldef := def) l = ldef;
            else throw TypePalUsage("Argument `def` of `defineInScope` should be `Tree` or `loc`, found <typeOf(def)>");
            
            id = unescapeName(id);
            if(info is defLub){
                throw TypePalUsage("`defLub` cannot be used in combination with `defineInScope`");
            } else {
                defines += <definingScope, id, idRole, l, info>;
            }
        } else {
            throw TypePalUsage("Cannot call `defineInScope` on Collector after `run`");
        }
    }
       
    void _use(Tree occ, set[IdRole] idRoles) {
        if(building){
          //if(currentScope == globalScope) throw TypePalUsage("`use` requires a user-defined scope; missing `enterScope`");
           uses += use(unescapeName("<occ>"), getLoc(occ), currentScope, idRoles);
        } else {
            throw TypePalUsage("Cannot call `use` on Collector after `run`");
        }
    }
    
    void _useLub(Tree occ, set[IdRole] idRoles) {
        if(building){
           if("<occ>" == "ddd") println("*** useLub: <occ>, <getLoc(occ)>");
           lubUsesPerLubScope[currentLubScope] += <unescapeName("<occ>"), currentScope, idRoles, getLoc(occ)>;
        } else {
            throw TypePalUsage("Cannot call `useLub` on Collector after `run`");
        }
    }
    
    void _useViaPath(Tree occ, set[IdRole] idRoles, PathRole pathRole) {
        if(building){
            u = use(unescapeName("<occ>"), getLoc(occ), currentScope, idRoles);
            uses += u;
            referPaths += {refer(u, pathRole)};
        } else {
            throw TypePalUsage("Cannot call `useViaPath` on Collector after `run`");
        }
    }
    
    AType(Solver) makeGetTypeInNamedType(Tree container, set[IdRole] idRolesCont, Tree selector, set[IdRole] idRolesSel, loc scope){
        return AType(Solver s) { 
            return s.getTypeInNamedType(container, idRolesCont, selector, idRolesSel, scope);
         };
    }
    
    void _useViaNamedType(Tree container, set[IdRole] idRolesCont, Tree selector, set[IdRole] idRolesSel){
        if(building){
            name = unescapeName("<selector>");
            sloc = getLoc(selector);
            indirectUses += use(name, sloc, currentScope, idRolesSel);
            calculators[sloc] = calculate("`<name>`", sloc, currentScope, [getLoc(container)],  false, makeGetTypeInNamedType(container, idRolesCont, selector, idRolesSel, currentScope));
  
        } else {
            throw TypePalUsage("Cannot call `useViaNamedType` on Collector after `run`");
        }
    }
   
    void _useQualified(list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles){
        if(building){
           uses += useq([unescapeName(id) | id <- ids], getLoc(occ), currentScope, idRoles, qualifierRoles);
        } else {
            throw TypePalUsage("Cannot call `useQualified` on Collector after `run`");
        }  
     }
     void _useQualifiedViaPath(list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathRole pathRole){
        if(building){
            u = useq([unescapeName(id) | id <- ids], getLoc(occ), currentScope, idRoles, qualifierRoles);
            uses += [u];
            referPaths += {refer(u, pathRole)};
        } else {
            throw TypePalUsage("Cannot call `useQualifiedViaPath` on Collector after `run`");
        } 
    }
    void _enterScope(Tree inner){
        enterScope(inner);
    }
    
    void _enterLubScope(Tree inner){
        enterScope(inner, lubScope=true);
    }
    
    void enterScope(Tree inner, bool lubScope=false){
        if(building){
           innerLoc = getLoc(inner);
            if(innerLoc == rootScope){
              currentScope = innerLoc;
              scopeStack = push(<innerLoc, lubScope, ()>, scopeStack);
           } else { //if(innerLoc != currentScope){
              scopes[innerLoc] = currentScope; 
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
           //else 
           //if(innerLoc == rootScope){
           //   currentScope = innerLoc;
           //   scopeStack = push(<innerLoc, lubScope, ()>, scopeStack);
           //} else {
           //   ;// do nothing throw TypePalUsage("Cannot call `enterScope` with inner scope <innerLoc> that is equal to currentScope");
           //}
        } else {
          throw TypePalUsage("Cannot call `enterScope` on Collector after `run`");
        }
    }
    
    void _leaveScope(Tree inner){
        if(building){
           innerLoc = getLoc(inner);
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
              throw TypePalUsage("Cannot call `leaveScope` with scope <inner> that is not the current scope"); 
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
                 scopeStack =  scopeStack[0..i] + <scope, lubScope, scopeInfo2> + scopeStack[i+1..];
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
                for(<loc scope, lubScope, map[ScopeRole,value] scopeInfo> <- scopeStack, scopeRole in scopeInfo){
                    append <scope, scopeInfo[scopeRole]>;
                }
            return res;
        } else {
           throw TypePalUsage("Cannot call `getScopeInfo` on Collector after `run`");
        }
    }
    
    loc _getScope(){
        if(building){
           if(currentScope == globalScope) throw TypePalUsage("`getScope` requires a user-defined scope; missing `enterScope`");
            return currentScope;
        } else {
            throw TypePalUsage("Cannot call `getScope` on Collector after `run`");
        }
    }
   
    void _require(str name, Tree src, list[value] dependencies, void(Solver s) preds){ 
        if(building){
           openReqs += { openReq(name, getLoc(src), currentScope, dependenciesAslocList(dependencies), false, preds) };
        } else {
            throw TypePalUsage("Cannot call `require` on Collector after `run`");
        }
    } 
    
    void _requireEager(str name, Tree src, list[value] dependencies, void(Solver s) preds){ 
        if(building){
           openReqs += { openReq(name, getLoc(src), currentScope, dependenciesAslocList(dependencies), true, preds) };
        } else {
            throw TypePalUsage("Cannot call `require` on Collector after `run`");
        }
    } 
    
    void _fact(Tree tree, AType tp){  
        if(building){
           openFacts += { openFact(getLoc(tree), {}, AType (Solver s){ return tp; } /*makeClos1(tp)*/) };
        } else {
            throw TypePalUsage("Cannot call `atomicFact` on Collector after `run`");
        }
    }
    
    void _calculate(str name, Tree src, list[value] dependencies, AType(Solver s) calculator){
        if(building){
           calculators[getLoc(src)] = calculate(name, getLoc(src), currentScope, dependenciesAslocList(dependencies),  false, calculator);
        } else {
            throw TypePalUsage("Cannot call `calculate` on Collector after `run`");
        }
    }
    
    void _calculateEager(str name, Tree src, list[value] dependencies, AType(Solver s) calculator){
        if(building){
           calculators[getLoc(src)] = calculate(name, getLoc(src), currentScope, dependenciesAslocList(dependencies),  true, calculator);
        } else {
            throw TypePalUsage("Cannot call `calculateEager` on Collector after `run`");
        }
    }
    
    AType(Solver) makeSameTypeCalculator(Tree src){
        return AType(Solver s) { return s.getType(src); };
    }
    
    void _sameType(Tree target, Tree src){
        if(building){
            ltarget = getLoc(target);
            calculators[ltarget] = calculate("sameType", ltarget, currentScope, [getLoc(src)],  false, makeSameTypeCalculator(src));
        } else {
            throw TypePalUsage("Cannot call `sameType` on Collector after `run`");
        }
    }
    
    bool _report(FailMessage fm){
       if(building){
          msg = toMessage(fm, defaultGetType);
          openReqs += { openReq("error", msg.at, currentScope, [], true, makeClosError(msg)) };
          return true;
       } else {
            throw TypePalUsage("Cannot call `report` on Collector after `run`");
       }
    }
    
     bool _reports(set[FailMessage] fms){
       if(building){
          msgs = {toMessage(fm, defaultGetType) | fm <- fms};
          openReqs += { openReq("error", getFirstFrom(msgs).at, currentScope, [], true, makeClosErrors(msgs)) };
          return true;
       } else {
            throw TypePalUsage("Cannot call `reports` on Collector after `run`");
       }
    }
    
    AType _newTypeVar(Tree src){
        if(building){
            tvLoc = getLoc(src);
            //ntypevar += 1;
            //qs = tvLoc.query;
            //qu = "uid=<ntypevar>";
            //tvLoc.query = isEmpty(qs) ? qu : "<qs>&<qu>";
            return tvar(tvLoc);
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
    
   // Merge all lubDefs and appoint a definition to refer to
    
    Define mergeLubDefs(str id, loc scope, rel[IdRole role, loc defined, DefInfo defInfo] lubDefs){
        deps = {}; getATypes = [];
        defineds = {};
        loc firstDefined = |undef:///|;
        roles = {};
        for(tuple[IdRole role, loc defined, DefInfo defInfo] info <- lubDefs){
            roles += info.role;
            defineds += info.defined;
            if(firstDefined == |undef:///| || info.defined.offset < firstDefined.offset){
                firstDefined = info.defined;
            }
            deps += info.defInfo.dependsOn;
            getATypes += info.defInfo.getATypes;
        }
        if({role} := roles){
            res = <scope, id, role, firstDefined, defLub(deps - defineds, defineds, getATypes)>;
            //println("mergeLubDefs: add define:");  iprintln(res);
            return res;
        } else 
             throw TypePalUsage("LubDefs should use a single role, found <roles>");
    }
    
    bool fixed_define_in_outer_scope(str id, loc lubScope){
        dbg = id in {"reachableTypes"};
        if(dbg) println("fixed_define_in_outer_scope: <id>, <lubScope>");
        outer = lubScope;
        while(scopes[outer]?){
            outer = scopes[outer];
            //println("outer: <outer>");
            //println("definesPerLubScope[outer] ? {}: <definesPerLubScope[outer] ? {}>");
            for(d: <loc scope, id, variableId(), loc defined, DefInfo defInfo> <- definesPerLubScope[outer] ? {}){
                if(dbg) println("fixed_define_in_outer_scope: <d>");
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
    // alias LubDefine2 = tuple[str id, loc scope, IdRole idRole, loc defined, DefInfo defInfo]; 
                
     set[Define] finalizeDefines(loc lubScope){
        //println("finalizeDefines: <lubScope>, <definesPerLubScope[lubScope]>");
        set[Define] extra_defines = {};
       
        rel[loc,loc] containment = scopesPerLubScope[lubScope]* + <lubScope,lubScope>;
        set[loc] allScopes = carrier(containment);
        
        set[LubDefine2] deflubs_in_lubscope = lubDefinesPerLubScope[lubScope];
        set[str] deflub_names = deflubs_in_lubscope<0>;
        rel[str id, loc idScope, set[IdRole] idRoles, loc occ] uselubs_in_lubscope = lubUsesPerLubScope[lubScope];  
         
        
        set[Define] local_fixed_defines = definesPerLubScope[lubScope];
        extra_defines += local_fixed_defines;
        
        rel[str, loc] local_fixed_defines_scope = local_fixed_defines<1,0>;
        set[str] ids_with_fixed_def = domain(local_fixed_defines_scope);
        
        for(str id <- deflub_names){
            set[loc] id_defined_in_scopes = deflubs_in_lubscope[id]<0>;
            id_defined_in_scopes = { sc1 | sc1 <- id_defined_in_scopes, isEmpty(containment) || !any(sc2 <- id_defined_in_scopes, sc1 != sc2, <sc2, sc1> in containment)};
            
            //println("Consider <id>, defined in scopes <id_defined_in_scopes>");
            //println("local_fixed_defines: <local_fixed_defines>");
            //println("local_fixed_defines[lubScope, id]: <local_fixed_defines[lubScope, id]>");
            
            if({fixedDef} := local_fixed_defines[lubScope, id]){   // Definition exists with fixed type in the lubScope; Use it instead of the lubDefines          
               //println("---top level fixedDef: <fixedDef> in <lubScope>");
               for(<IdRole role, loc defined, DefInfo defInfo> <- deflubs_in_lubscope[id, allScopes]){
                   u = use(id, defined, lubScope, {role});
                   //println("add: <u>");
                   uses += u;
               }
            } else if(fixed_define_in_outer_scope(id, lubScope)){   // Definition exists with fixed type in a surrounding scope; Use it instead of the lubDefines          
               //println("---top level fixedDef: <fixedDef> in <lubScope>");
               for(<IdRole role, loc defined, DefInfo defInfo> <- deflubs_in_lubscope[id, allScopes]){
                   u = use(id, defined, lubScope, {role});
                   //println("add: <u>");
                   uses += u;
               }
            } else if(id in ids_with_fixed_def){ // Definition(s) with fixed type exist in one or more subscopes, use them instead of the lubDefines 
                //println("---fixed def(s) in subscopes: <local_fixed_defines_scope[id]>");
                //println("containment: <containment>");
                for(scope <- allScopes){
                    if(scope in local_fixed_defines_scope[id]){
                        for(<IdRole role, loc defined, DefInfo defInfo> <- deflubs_in_lubscope[id, containment[scope]]){
                            u = use(id, defined, scope, {role});
                            //println("add: <u>");
                            uses += u;
                        }
                    } else {
                        id_dfs = deflubs_in_lubscope[id, scope];
                        if(!isEmpty(id_dfs)) {
                            extra_defines += mergeLubDefs(id, scope, id_dfs);
                        }
                    }
                }
            } else if(lubScope in id_defined_in_scopes){   // Definition exists in the lubScope without fixed type, merge all lubDefs
                //println("---toplevel lubDef");
                 id_dfs = deflubs_in_lubscope[id, containment[id_defined_in_scopes]];
                 if(!isEmpty(id_dfs)){
                    extra_defines += mergeLubDefs(id, lubScope, id_dfs);
                 }
           } else {                                     // Same id defined in one or more disjoint subscopes
             for(scope <- id_defined_in_scopes){
                if({fixedDef} := local_fixed_defines[scope, id]){ // defined in outer scope with fixed type
                   //println("fixedDef: <fixedDef> in inner scope <scope>");
                   // There exists a definition with fixed type in the inner scope, just use it instead of the lubDefines
                   for(<IdRole role, loc defined, DefInfo defInfo> <- deflubs_in_lubscope[id, containment[id_defined_in_scopes]]){
                       u = use(id, defined, scope, {role});
                      //println("add: <u>");
                       uses += u;
                   }
               } else {
                 extra_defines += mergeLubDefs(id, scope, deflubs_in_lubscope[id, containment[scope]]);
               }
             }
           }
        }
        
        // Transform uncovered lubUses into ordinary uses
    
        for(u: <str id, loc idScope, set[IdRole] idRoles, loc occ> <- uselubs_in_lubscope){
            //println("replace lubUse by <use(id, occ, idScope, idRoles)>");
            uses += use(id, occ, idScope, idRoles);
            uselubs_in_lubscope -= u;
        }
        
        definesPerLubScope = Map::delete(definesPerLubScope, lubScope);   // Remove all data recorded for this lubScope
        lubDefinesPerLubScope = Map::delete(lubDefinesPerLubScope, lubScope);
        lubUsesPerLubScope = Map::delete(lubUsesPerLubScope, lubScope);
        scopesPerLubScope = Map::delete(scopesPerLubScope, lubScope);
        
        return extra_defines;
    }
    
    void _addTModel(TModel tm){
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
    
    TModel resolvePath(TModel tm){
        msgs = [];
        int n = 0;
    
        referPaths = tm.referPaths;
        newPaths = {};
        
        lookupFun = config.lookup;
        
        while(!isEmpty(referPaths) && n < 3){    // explain this iteration count
            n += 1;
            for(rp <- referPaths){
                try {
                    u = rp.use;
                    //u.scope[fragment=""];
                    //u.occ[fragment=""];
                    foundDefs = lookupFun(tm, u);
                    if({def} := foundDefs){
                       //println("resolvePath: resolve <rp.use> to <def>");
                       newPaths += {<u.scope, rp.pathRole, def>};  
                    } else {
                        //// If only overloaded due to different time stamp, use most recent.
                        //<ok, def> = findMostRecentDef(foundDefs);
                        //if(ok){
                        //    tm.paths += {<rp.use.scope, rp.pathRole, def>};
                        // } else { 
                            msgs += error("Name `<u.id>` is ambiguous <foundDefs>", u.occ);
                         //}
                    }
                    referPaths -= {rp}; 
                }
                catch:{
                    println("Lookup for <rp> fails"); 
                    msgs += error("Name `<rp.use.id>` not found", rp.use.occ);
                }
            }
        }
        tm.paths += newPaths;
        tm.referPaths = referPaths;
        for(rp <- referPaths){
            msgs += error("Reference to name `<rp.use.id>` cannot be resolved", rp.use.occ);
        }
        tm.messages += msgs;
        return tm;
    }
    
    TModel _run(){
        if(building){
           building = false;
           
           if(size(scopeStack) == 0){
                throw TypePalUsage("Bottom entry missing from scopeStack: more leaveScopes than enterScopes");
           }
           
           if(size(scopeStack) > 1){
                unclosed = [scope | <loc scope, bool lubScope, map[ScopeRole, value] scopeInfo> <- scopeStack];
                throw TypePalUsage("Missing `leaveScope`(s): unclosed scopes <unclosed>");
           }
           
           tm = tmodel();
           tm.config = config;
           defines = finalizeDefines();
           tm.defines = defines;
           tm.scopes = scopes;  scopes = ();
           tm.paths = paths;
           tm.referPaths = referPaths;
           tm.namedTypes = namedTypes; namedTypes = ();
           tm.uses = uses;      uses = [];
           tm.indirectUses = indirectUses; indirectUses = [];
           
           tm.calculators = calculators;
           tm.facts = facts;            facts = ();
           tm.openFacts = openFacts;    openFacts = {};    
           tm.openReqs = openReqs;  
//         tm.tvScopes = tvScopes;      tvScopes = ();
           tm.store = storeVals;        storeVals = ();
           tm.definitions = ( def.defined : def | Define def <- defines);
           definesMap = ();
           for(<loc scope, str id, IdRole idRole, loc defined, DefInfo defInfo> <- defines){
                dm = ();
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
           return resolvePath(tm); 
        } else {
           throw TypePalUsage("Cannot call `run` on Collector after `run`");
        }
    }
    
    return collector(_define,
                    _defineInScope,
                    _use, 
                    _useLub,
                    _useViaPath,
                    _useViaNamedType,
                    _useQualified, 
                    _useQualifiedViaPath, 
                    _enterScope, 
                    _enterLubScope,
                    _leaveScope,
                    _setScopeInfo,
                    _getScopeInfo,
                    _getScope,
                    _require, 
                    _requireEager,
                    _fact,
                    _calculate, 
                    _calculateEager,
                    _sameType,
                    _report, 
                    _reports,
                    _newTypeVar, 
                    _push,
                    _pop,
                    _top,
                    _getStack,
                    _clearStack,
                    _addTModel,
                    _getConfig,
                    _setConfig,
                    _run); 
}
