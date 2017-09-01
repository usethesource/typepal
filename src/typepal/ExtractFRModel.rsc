module typepal::ExtractFRModel

import Node;
import ParseTree;
import String;
extend typepal::ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc name)                  // type variable, used for type inference
    | useType(Use use)                // Use a type defined elsewhere
    | lub(AType atype1, AType atype2)
    | listType(list[AType] atypes)
    ;

// Pretty print ATypes
str AType2String(tvar(loc name))    = "<name>";
str AType2String(useType(Use use)) = "<getId(use)>";
str AType2String(listType(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [AType2String(a) | a <- atypes]);
default str AType2String(AType tp) = "<tp>";

// AType utilities
bool isTypeVariable(loc tv) = tv.scheme == "typevar"; 

set[loc] extractTypeDependencies(AType tp) 
    = { use.occ | /useType(Use use) := tp };

bool allDependenciesKnown(set[loc] deps, map[loc,AType] facts)
    = (isEmpty(deps) || all(dep <- deps, facts[dep]?));

list[Key] dependenciesAsKeyList(list[value] dependencies){
    return 
        for(d <- dependencies){
            if(Tree t := d){
                append t@\loc;
            } else {
                throw "Dependency should be a tree, found <d>";
            }
        };
} 

set[Key] dependenciesAsKeys(list[value] dependencies)
    = toSet(dependenciesAsKeyList(dependencies));

// Definition info used during type checking
data DefInfo
    = defType(AType atype)                              // Explicitly given AType
    | defType(set[Key] dependsOn, AType() getAType)     // AType given as callback.
    | defLub(list[AType] atypes)                                              // redefine previous definition
    | defLub(set[Key] dependsOn, set[Key] defines, list[AType()] getATypes)   // redefine previous definition
    ;

DefInfo defType(list[value] dependsOn, AType() getAType)
    = defType(dependenciesAsKeys(dependsOn), getAType);
    
DefInfo defLub(list[value] dependsOn, AType() getAType)
    = defLub(dependenciesAsKeys(dependsOn), {}, [getAType]);
    
// Errors found during type checking  
data ErrorHandler
    = onError(loc where, str msg)
    | noError()
    ;
   
ErrorHandler onError(Tree t, str msg) = onError(t@\loc, msg);

void reportError(Tree t, str msg){
    throw error(msg, t@\loc);
}

// The basic ingredients for type checking: facts, requirements and overloads

// Fact about location src, given dependencies and an AType callback
data Fact
    = openFact(loc src, set[loc] dependsOn, AType() getAType)
    | openFact(set[loc] srcs, set[loc] dependsOn, list[AType()] getATypes)
    ;

// A named requirement for location src, given dependencies and a callback predicate
data Requirement
    = openReq(str name, loc src, set[loc] dependsOn,  void() preds);

// Named type calculator for location src, given args, and resolve callback    
data Calculator
    = calculate(str name, loc src, list[loc] dependsOn, AType() calculator);

data FRModel (
        map[loc,Calculator] calculators = (),
        map[loc,AType] facts = (), 
        set[Fact] openFacts = {},
        set[Requirement] openReqs = {},
        map[loc,loc] tvScopes = ()
        );

alias Key = loc;

default Tree define(Tree tree, Tree scope, FRBuilder frb) {
   //println("Default define <tree>");
   return scope;
}

default void collect(Tree tree, Tree scope, FRBuilder frb) { 
    //println("Default collect <tree>");
}

default FRModel initializeFRModel(FRModel frm) = frm;

default FRModel enhanceFRModel(FRModel frm) = frm;

FRModel extractFRModel(Tree root, FRBuilder frb){
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
        void (Tree src, AType tp) atomicFact,
        void (Tree src, list[value] dependencies, AType() getAType) fact,
        void (str name, Tree src, list[value] dependencies, AType() calculator) calculate,
        void (Tree src, str msg) error,
        AType (Tree scope) newTypeVar,
        FRModel () build
      ); 

AType() makeClos1(AType tp) = AType (){ return tp; };                   // TODO: workaround for compiler glitch
void() makeClos2(Tree src, str msg) = void(){ reportError(src, msg); };
                          
FRBuilder newFRBuilder(bool debug = false){
        
    Defines defines = {};
    Defines lubDefines = {};
    rel[loc, str, IdRole] lubKeys = {};
    Scopes scopes = ();
    Paths paths = {};
    ReferPaths referPaths = {};
    Uses uses = [];
    
    map[loc,Calculator] calculators = ();
    map[loc,AType] facts = ();
    set[Fact] openFacts = {};
    set[Requirement] openReqs = {};
    int ntypevar = -1;
    map[loc,loc] tvScopes = ();
    luDebug = debug;
    
    void _define(Tree scope, str id, IdRole idRole, Tree def, DefInfo info){
        if(info is defLub){
            lubDefines += {<scope@\loc, id, idRole, def@\loc, info>};
            lubKeys += <scope@\loc, id, idRole>;
        } else {
            defines += {<scope@\loc, id, idRole, def@\loc, info>};
        }
    }
       
    void _use(Tree scope, Tree occ, set[IdRole] idRoles) {
        uses += [use("<occ>", occ@\loc, scope@\loc, idRoles)];
    }
    
    void _use_ref(Tree scope, Tree occ, set[IdRole] idRoles, PathLabel pathLabel) {
        u = use("<occ>", occ@\loc, scope@\loc, idRoles);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _use_qual(Tree scope, list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles){
        uses += [useq(ids, occ@\loc, scope@\loc, idRoles, qualifierRoles)];
    }
     void _use_qual_ref(Tree scope, list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel){
        u = useq(ids, occ@\loc, scope@\loc, idRoles, qualifierRoles);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _addScope(Tree inner, Tree outer) { if(inner@\loc != outer@\loc) scopes[inner@\loc] = outer@\loc; }
     
    
    void _require(str name, Tree src, list[value] dependencies, void() preds){ 
        openReqs += { openReq(name, src@\loc, dependenciesAsKeys(dependencies),  preds) };
    } 
    
    void _fact1(Tree tree, AType tp){  
        deps = extractTypeDependencies(tp);
        openFacts += { openFact(tree@\loc, deps, makeClos1(tp)) };
    }
    
    void _fact2(Tree tree, list[value] dependencies, AType() getAType){
        openFacts += { openFact( tree@\loc, dependenciesAsKeys(dependencies), getAType) };
    }
    
    void _calculate(str name, Tree src, list[value] dependencies, AType() calculator){
        calculators[src@\loc] = calculate(name, src@\loc, dependenciesAsKeyList(dependencies),  calculator);
    }
    
    void _error(Tree src, str msg){
        openReqs += { openReq("error", src@\loc, {}, makeClos2(src, msg)) };
    }
    
    AType _newTypeVar(Tree scope){
        ntypevar += 1;
        s = right("<ntypevar>", 10, "0");
        tv = |typevar:///<s>|;
        tvScopes[tv] = scope@\loc;
        return tvar(tv);
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
                    if(!firstDefined? || info.defined.begin.line < firstDefined.begin.line){
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
       
       return frm; 
    }
    
    return frbuilder(_define, _use, _use_ref, _use_qual, _use_qual_ref, _addScope, _require, _fact1, _fact2, _calculate, _error,  _newTypeVar, _build); 
}