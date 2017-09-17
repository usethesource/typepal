@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module typepal::ExtractFRModel

import Node;
import ParseTree;
import String;
extend typepal::ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc name)                            // type variable, used for type inference
    | useType(Use use)                          // Use a type defined elsewhere
    | lazyLub(list[AType] atypes)               // lazily computed LUB of a list of types
    | atypeList(list[AType] atypes)              // built-in list-of-ATypes type
    | overloadedType(rel[Key, AType] overloads) // built-in-overloaded type; each key provides an alternative type
    ;

// Pretty print ATypes
str AType2String(tvar(loc name))    = "<name>";
str AType2String(useType(Use use)) = "<getId(use)>";
str AType2String(lazyLub(list[AType] atypes)) = "lub(<atypes>))";
str AType2String(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [AType2String(a) | a <- atypes]);
str AType2String(overloadedType(rel[Key, AType] overloads)) = "overloaded(" + intercalate(", ", [AType2String(t) | <k, t> <- overloads]) + ")";
default str AType2String(AType tp) = "<tp>";

// AType utilities
bool isTypeVariable(loc tv) = tv.scheme == "typevar"; 

loc getLoc(Tree t) = t@\loc ? t.args[0]@\loc;
    
set[loc] extractTypeDependencies(AType tp) 
    = { use.occ | /useType(Use use) := tp } /*+ { src | /tvar(loc src) := tp }*/;


list[Key] dependenciesAsKeyList(list[value] dependencies){
    return 
        for(d <- dependencies){
            if(Tree t := d){
                append getLoc(t);
            } else {
                throw "Dependency should be a tree, found <d>";
            }
        };
} 

set[Key] dependenciesAsKeys(list[value] dependencies)
    = toSet(dependenciesAsKeyList(dependencies));

// Definition info used during type checking
data DefInfo
    = defType(AType atype)                                                    // Explicitly given AType
    | defType(set[Key] dependsOn, AType() getAType)                           // AType given as callback.
    | defLub(list[AType] atypes)                                              // redefine previous definition
    | defLub(set[Key] dependsOn, set[Key] defines, list[AType()] getATypes)   // redefine previous definition
    ;

DefInfo defType(list[value] dependsOn, AType() getAType)
    = defType(dependenciesAsKeys(dependsOn), getAType);
    
DefInfo defLub(list[value] dependsOn, AType() getAType)
    = defLub(dependenciesAsKeys(dependsOn), {}, [getAType]);
    
// Errors found during type checking  
data ErrorHandler
    = onError(loc where, str msg, list[value] args)
    | noError()
    ;
   
ErrorHandler onError(Tree t, str msg, value args...) = onError(getLoc(t), msg, args);

str v2s(AType t)            = "`<AType2String(t)>`";
//str v2s(Tree t)             = "`<AType2String(typeof(t))>`";
str v2s(str s)              = "`<s>`";
str v2s(int n)              = "<n>";
str v2s(list[value] vals)   = intercalateAnd([v2s(vl) | vl <- vals]);
default str v2s(value v)    = "`<v>`";

str intercalateAnd(list[str] strs){
    switch(size(strs)){
      case 0: return "";
      case 1: return strs[0];
      default: 
              return intercalate(", ", strs[0..-1]) + " and " + strs[-1];
      };
}

str interpolate(str msg, value args...){
    parts = split("%", msg);
    nparts = size(parts);
    int iargs = 0;
    int nargs = size(args);
    interpolated =
        for(int i <- index(parts)){
            append parts[i];
            if(i > 0 && isEmpty(parts[i])) { 
                append "%";
            } else {
                if(i < nparts-1 && !isEmpty(parts[i+1])){
                    if( iargs < nargs){
                        append v2s(args[iargs]);
                        iargs += 1;
                    } else {
                        throw "Interpolation: too few args for <msg>";
                    }
                }
            }
        }
    if(iargs < nargs){
        interpolated += [v2s(a) | a <- args[iargs..]];
    }
    return intercalate("", interpolated);
}
void reportError(Tree t, str msg, value args...){
    throw error(interpolate(msg, args), getLoc(t));
}

void reportWarning(Tree t, str msg, value args...){
    throw warning(interpolate(msg, args), getLoc(t));
}

void reportInfo(Tree t, str msg, value args...){
    throw info(interpolate(msg, args), getLoc(t));
}

// The basic ingredients for type checking: facts, requirements and overloads

// Fact about location src, given dependencies and an AType callback
data Fact
    = openFact(loc src, set[loc] dependsOn, AType() getAType)
    | openFact(set[loc] srcs, set[loc] dependsOn, list[AType()] getATypes)
    ;

// A named requirement for location src, given dependencies and a callback predicate
data Requirement
    = openReq(str name, loc src, set[loc] dependsOn, bool eager, void() preds);

// Named type calculator for location src, given args, and resolve callback    
data Calculator
    = calculate(str name, loc src, set[loc] dependsOn, bool eager, AType() calculator);

// The basic Fact & Requirement Model; can be extended in specific type checkers
data FRModel (
        map[loc,Calculator] calculators = (),
        map[loc,AType] facts = (), 
        set[Fact] openFacts = {},
        set[Requirement] openReqs = {},
        map[loc,loc] tvScopes = (),
        set[Message] messages = {},
        rel[str,value] store = {}
        );

alias Key = loc;

// Default definition for define; to be overridden in speicific type checker
default Tree define(Tree tree, Tree scope, FRBuilder frb) {
   //println("Default define <tree>");
   return scope;
}

// Default definition for collect; to be overridden in specific type checker
default void collect(Tree tree, Tree scope, FRBuilder frb) { 
    //println("Default collect <tree>");
}

// Default definition for initializeFRModel; may be overridden in specific type checker to add initial type info
default FRModel initializeFRModel(FRModel frm) = frm;

// Default definition for enhanceFRModel; 
// may be overridden in specific type checker to enhance extracted facts and requirements before validation
default FRModel enhanceFRModel(FRModel frm) = frm;

FRModel extractFRModel(Tree root, FRBuilder frb){
    //println("extractFRModel: <root>");
    extract2(root, root, frb);
    frm = enhanceFRModel(frb.build());
    if(luDebug) printFRModel(frm);
    int n = 0;
    if(luDebug) println("&&&&&&&&&&&&&&&&&&&&& resolving referPath &&&&&&&&&&&&&&&&&&&&");
    while(!isEmpty(frm.referPaths) && n < 3){    // explain this iteration count
        n += 1;
        for(c <- frm.referPaths){
            try {
                def = lookup(frm, c.use);
                /*if(debug)*/ println("extractFRModel: resolve <c.use> to <def>");
                frm.paths += {<c.use.scope, c.pathLabel, def>};
                frm.referPaths -= {c}; 
            }
            catch:
                println("Lookup for <c> fails"); 
        }
    }
    if(!isEmpty(frm.referPaths)){
        println("&&&&&&&&&&&&&&&&&&& Could not solve path contributions");
    }
    return frm;
}

void extract2(currentTree: appl(Production _, list[Tree] args), Tree currentScope, FRBuilder frb){
   //println("extract2: <currentTree>");
   newScope = define(currentTree, currentScope, frb);
   frb.addScope(newScope, currentScope);
   collect(currentTree, newScope, frb);
   bool nonLayout = true;
   for(Tree arg <- args){
       if(nonLayout && !(arg is char))
          extract2(arg, newScope, frb);
       nonLayout = !nonLayout;
   }
}

default void extract2(Tree root, Tree currentScope, FRBuilder frb) {
    //println("default extract2: <getName(root)>");
}

data FRBuilder 
    = frbuilder(
        Tree (Tree scope, str id, IdRole idRole, Tree def, DefInfo info) define,
        void (Tree scope, Tree occ, set[IdRole] idRoles) use,
        void (Tree scope, Tree occ, set[IdRole] idRoles, PathLabel pathLabel) use_ref,
        void (Tree scope, list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles) use_qual,
        void (Tree scope, list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel) use_qual_ref,   
        void (Tree inner, Tree outer) addScope,
       
        void (str name, Tree src, list[value] dependencies, void() preds) require,
        void (str name, Tree src, list[value] dependencies, void() preds) requireEager,
        void (Tree src, AType tp) atomicFact,
        void (Tree src, list[value] dependencies, AType() getAType) fact,
        void (str name, Tree src, list[value] dependencies, AType() calculator) calculate,
        void (str name, Tree src, list[value] dependencies, AType() calculator) calculateEager,
        void (Tree src, str msg, list[value] args) reportError,
        void (Tree src, str msg, list[value] args) reportWarning,
        void (Tree src, str msg, list[value] args) reportInfo,
        AType (Tree scope) newTypeVar,
        void (str key, value val) store,
        FRModel () build
      ); 

AType() makeClos1(AType tp) = AType (){ return tp; };                   // TODO: workaround for compiler glitch
void() makeClosError(Tree src, str msg, list[value] args) = void(){ reportError(src, msg, args); };
void() makeClosWarning(Tree src, str msg, list[value] args) = void(){ reportWarning(src, msg, args); };
void() makeClosInfo(Tree src, str msg, list[value] args) = void(){ reportInfo(src, msg, args); };
                          
FRBuilder newFRBuilder(bool debug = false){
        
    Defines defines = {};
    Defines lubDefines = {};
    rel[loc, str, IdRole] lubKeys = {};
    Scopes scopes = ();
    Paths paths = {};
    ReferPaths referPaths = {};
    Uses uses = [];
    rel[str,value] storeVals = {};
    
    map[loc,Calculator] calculators = ();
    map[loc,AType] facts = ();
    set[Fact] openFacts = {};
    set[Requirement] openReqs = {};
    int ntypevar = -1;
    map[loc,loc] tvScopes = ();
    luDebug = debug;
    
    bool building = true;
    
    void _define(Tree scope, str id, IdRole idRole, Tree def, DefInfo info){
        if(building){
            if(info is defLub){
                lubDefines += {<getLoc(scope), id, idRole, getLoc(def), info>};
                lubKeys += <getLoc(scope), id, idRole>;
            } else {
                defines += {<getLoc(scope), id, idRole, getLoc(def), info>};
            }
        } else {
            throw "Cannot call `define` on FRBuilder after `build`";
        }
    }
       
    void _use(Tree scope, Tree occ, set[IdRole] idRoles) {
        if(building){
           uses += [use("<occ>", getLoc(occ), getLoc(scope), idRoles)];
        } else {
            throw "Cannot call `use` on FRBuilder after `build`";
        }
    }
    
    void _use_ref(Tree scope, Tree occ, set[IdRole] idRoles, PathLabel pathLabel) {
        if(building){
            u = use("<occ>", getLoc(occ), getLoc(scope), idRoles);
            uses += [u];
            referPaths += {refer(u, pathLabel)};
        } else {
            throw "Cannot call `use_ref` on FRBuilder after `build`";
        }
    }
    
    void _use_qual(Tree scope, list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles){
        if(building){
           uses += [useq(ids, getLoc(occ), getLoc(scope), idRoles, qualifierRoles)];
        } else {
            throw "Cannot call `use_qual` on FRBuilder after `build`";
        }  
     }
     void _use_qual_ref(Tree scope, list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel){
        if(building){
            u = useq(ids, getLoc(occ), getLoc(scope), idRoles, qualifierRoles);
            uses += [u];
            referPaths += {refer(u, pathLabel)};
        } else {
            throw "Cannot call `use_qual_ref` on FRBuilder after `build`";
        } 
    }
    
    void _addScope(Tree inner, Tree outer) { 
        if(building){
            innerLoc = getLoc(inner);
            outerLoc = getLoc(outer);
            if(innerLoc != outerLoc) scopes[innerLoc] = outerLoc; 
        } else {
            throw "Cannot call `addScope` on FRBuilder after `build`";
        }
    }
     
    
    void _require(str name, Tree src, list[value] dependencies, void() preds){ 
        if(building){
           openReqs += { openReq(name, getLoc(src), dependenciesAsKeys(dependencies), false, preds) };
        } else {
            throw "Cannot call `require` on FRBuilder after `build`";
        }
    } 
    
    void _requireEager(str name, Tree src, list[value] dependencies, void() preds){ 
        if(building){
           openReqs += { openReq(name, getLoc(src), dependenciesAsKeys(dependencies), true, preds) };
        } else {
            throw "Cannot call `require` on FRBuilder after `build`";
        }
    } 
    
    void _fact1(Tree tree, AType tp){  
        if(building){
           deps = extractTypeDependencies(tp);
           openFacts += { openFact(getLoc(tree), deps, makeClos1(tp)) };
        } else {
            throw "Cannot call `atomicFact` on FRBuilder after `build`";
        }
    }
    
    void _fact2(Tree tree, list[value] dependencies, AType() getAType){
        if(building){
           openFacts += { openFact(getLoc(tree), dependenciesAsKeys(dependencies), getAType) };
        } else {
            throw "Cannot call `fact` on FRBuilder after `build`";
        }
    }
    
    void _calculate(str name, Tree src, list[value] dependencies, AType() calculator){
        if(building){
           calculators[getLoc(src)] = calculate(name, getLoc(src), dependenciesAsKeys(dependencies),  false, calculator);
        } else {
            throw "Cannot call `calculate` on FRBuilder after `build`";
        }
    }
    void _calculateEager(str name, Tree src, list[value] dependencies, AType() calculator){
        if(building){
           calculators[getLoc(src)] = calculate(name, getLoc(src), dependenciesAsKeys(dependencies),  true, calculator);
        } else {
            throw "Cannot call `calculateOpen` on FRBuilder after `build`";
        }
    }
    
    void _reportError(Tree src, str msg, list[value] args){
       if(building){
          openReqs += { openReq("error", getLoc(src), {}, true, makeClosError(src, msg, args)) };
       } else {
            throw "Cannot call `reportError` on FRBuilder after `build`";
       }
    }
    
    void _reportWarning(Tree src, str msg, list[value] args){
        if(building){
           openReqs += { openReq("warning", getLoc(src), {}, true, makeClosWarning(src, msg, args)) };
        } else {
            throw "Cannot call `reportWarning` on FRBuilder after `build`";
        }
    }
    
    void _reportInfo(Tree src, str msg, list[value] args){
        if(building){
           openReqs += { openReq("info", getLoc(src), {}, true, makeClosInfo(src, msg, args)) };
        } else {
            throw "Cannot call `reportInfo` on FRBuilder after `build`";
        }
    }
    
    AType _newTypeVar(Tree scope){
        if(building){
            ntypevar += 1;
            s = right("<ntypevar>", 10, "0");
            tv = |typevar:///<s>|;
            tvScopes[tv] = getLoc(scope);
            return tvar(tv);
        } else {
            throw "Cannot call `newTypeVar` on FRBuilder after `build`";
        }
    }
    
    void _store(str key, value val){
        storeVals += <key, val>;
    }
    
    void finalizeDefines(){
        set[Define] extra_defines = {};
       
        for(<scope, id, role> <- lubKeys){
            //println("<scope>, <id>, <role>");
            if({fixedDef} := defines[scope, id, role]){
                for(<Key defined, DefInfo defInfo> <- lubDefines[scope, id, role]){
                    res = use(id, defined, scope, {role});
                    //println("add use: <res>");
                    uses += res;
                }
            } else { // No definition with fixed type
                deps = {}; getATypes = [];
                defineds = {};
                loc firstDefined;
                for(tuple[Key defined, DefInfo defInfo] info <- lubDefines[scope, id, role]){
                    defineds += info.defined;
                    if(!firstDefined? || info.defined.offset < firstDefined.offset){
                        firstDefined = info.defined;
                    }
                    deps += info.defInfo.dependsOn;
                    getATypes += info.defInfo.getATypes;
                }
              
                res = <scope, id, role, firstDefined, defLub(deps - defineds, defineds, getATypes)>;
                //println("add define: <res>");
                extra_defines += res;
            }
        }
        defines += extra_defines;
    }
    
    FRModel _build(){
        if(building){
           building = false;
           frm = frModel();
           finalizeDefines();
           frm.defines = defines;
           frm.scopes = scopes;
           frm.paths = paths;
           frm.referPaths = referPaths;
           frm.uses = uses;
           
           frm.calculators = calculators;
           frm.facts = facts;
           frm.openFacts = openFacts;
           frm.openReqs = openReqs;
           frm.tvScopes = tvScopes;
           frm.store = storeVals;
           
           return frm; 
        } else {
           throw "Cannot call `build` on FRBuilder after `build`";
        }
    }
    
    return frbuilder(_define, 
                     _use, 
                     _use_ref, 
                     _use_qual, 
                     _use_qual_ref, 
                     _addScope, 
                     _require, 
                     _requireEager,
                     _fact1, 
                     _fact2, 
                     _calculate, 
                     _calculateEager,
                     _reportError, 
                     _reportWarning, 
                     _reportInfo, 
                     _newTypeVar, 
                     _store,
                     _build); 
}
