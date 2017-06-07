module ExtractFRModel

import Node;
import ParseTree;
import String;
extend ScopeGraph;

alias FRModel = ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc name)                  // type variable, used for type inference
    | useType(Use use)                // Use a type defined elsewhere
    | listType(list[AType] atypes)
    ;

// Pretty print ATypes
str AType2String(tvar(loc name))    = "<name>";
str AType2String(useType(Use use)) = "<use.id>";
str AType2String(listType(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [AType2String(a) | a <- atypes]);
default str AType2String(AType tp) = "<tp>";

// AType utilities
bool isTypeVariable(loc tv) = tv.scheme == "typevar"; 

set[loc] extractTypeDependencies(AType tp) 
    = { use.scope | /useType(Use use) := tp };

bool allDependenciesKnown(set[loc] deps, map[loc,AType] facts)
    = (isEmpty(deps) || all(dep <- deps, facts[dep]?));

// Definition info used during type checking
data DefInfo
    = defInfo(AType atype)                              // Explicitly given AType
    | defInfo(list[Tree] dependsOn, AType() getAType)   // AType given as callback.
    ;
 
// Errors found during type checking  
data ErrorHandler
    = onError(loc where, str msg);
   
ErrorHandler onError(Tree t, str msg) = onError(t@\loc, msg);

void reportError(Tree t, str msg){
    throw error(msg, t@\loc);
}

// The basic ingredients for type checking: facts, requirements and overloads

// Fact about location src, given dependencies and an AType callback
data Fact
    = openFact(set[loc] dependsOn, loc src, AType() getAType);

// A named requirement for location src, given dependencies and a callback predicate
data Requirement
    = openReq(str name, set[loc] dependsOn, loc src, void() preds);

// Named overloading resolver for location src, given args, and resolve callback    
data Overload
    = overload(str name, list[loc] args, loc src,  AType() resolve);

data ScopeGraph (
        map[loc,Overload] overloads = (),
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

ScopeGraph extractScopesAndConstraints(Tree root, FRBuilder frb){
    extract2(root, root, frb);
    sg = frb.build();
    if(debug) printScopeGraph(sg);
    int n = 0;
    while(!isEmpty(sg.referPaths) && n < 3){    // explain this iteration count
        n += 1;
        for(c <- sg.referPaths){
            try {
                def = lookup(sg, c.use);
                if(debug) println("extract1: resolve <c.use> to <def>");
                sg.paths += {<c.use.scope, c.pathLabel, def>};
                sg.referPaths -= {c}; 
            }
            catch:; 
        }
    }
    if(!isEmpty(sg.referPaths)){
        println("Could not solve path contributions");
    }
    return sg;
}

void extract2(currentTree: appl(Production prod, list[Tree] args), Tree currentScope, FRBuilder frb){
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
        void (Tree scope, Idn id, IdRole idRole, Tree root, DefInfo info) define,
        void (Tree scope, Tree occ, set[IdRole] idRoles, int defLine) use,
        void (Tree scope, Tree occ, set[IdRole] idRoles, PathLabel pathLabel, int defLine) use_ref,
        void (Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, int defLine) use_qual,
        void (Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel, int defLine) use_qual_ref,   
        void (Tree inner, Tree outer) addScope,
       
        void (str name, Tree src, list[Tree] dependencies, void() preds) require,
        void (Tree src, AType tp) atomicFact,
        void (Tree src, list[Tree] dependencies, AType() getAType) fact,
        void (str name, Tree src, list[Tree] args, AType() resolver) overload,
        void (Tree src, str msg) error,
        AType (Tree scope) newTypeVar,
        FRModel () build
      ); 

AType() makeClos1(AType tp) = AType (){ return tp; };                   // TODO: workaround for compiler glitch
void() makeClos2(Tree src, str msg) = void(){ reportError(src, msg); };
                          
FRBuilder makeFRBuilder(){
        
    Defines defines = {};
    Scopes scopes = ();
    Paths paths = {};
    ReferPaths referPaths = {};
    Uses uses = [];
    
    map[loc,Overload]overloads = ();
    map[loc,AType] facts = ();
    set[Fact] openFacts = {};
    set[Requirement] openReqs = {};
    int ntypevar = -1;
    map[loc,loc] tvScopes = ();
    
    void _define(Tree scope, Idn id, IdRole idRole, Tree d, DefInfo info){
        defines += {<scope@\loc, id, idRole, d@\loc, info>};
    }
       
    void _use(Tree scope, Tree occ, set[IdRole] idRoles, int defLine) {
        uses += [use("<occ>", occ@\loc, scope@\loc, idRoles, defLine=defLine)];
    }
    
    void _use_ref(Tree scope, Tree occ, set[IdRole] idRoles, PathLabel pathLabel, int defLine) {
        u = use("<occ>", occ@\loc, scope@\loc, idRoles, defLine=defLine);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _use_qual(Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, int defLine){
        uses += [usen(ids, occ@\loc, scope@\loc, idRoles, qualifierRoles, defLine=defLine)];
    }
     void _use_qual_ref(Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel, int defLine){
        u = usen(ids, occ@\loc, scope@\loc, idRoles, qualifierRoles, defLine=defLine);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _addScope(Tree inner, Tree outer) { if(inner@\loc != outer@\loc) scopes[inner@\loc] = outer@\loc; }
     
    void _require(str name, Tree src, list[Tree] dependencies, void() preds){        
        deps = {d@\loc | d <- dependencies};        
        openReqs += { openReq(name, deps, src@\loc, preds) };
    } 
    
    void _fact1(Tree tree, AType tp){
        deps = extractTypeDependencies(tp);
        openFacts += { openFact(deps, tree@\loc, makeClos1(tp)) };
    }
    
    void _fact2(Tree tree, list[Tree] dependencies, AType() getAType){
        deps = { d@\loc | d <- dependencies };
        openFacts += { openFact(deps, tree@\loc, getAType) };
    }
    
    void _overload(str name, Tree src, list[Tree] args, AType() resolver){
        overloads[src@\loc] = overload(name, [arg@\loc | arg <- args], src@\loc, resolver);
    }
    
    void _error(Tree src, str msg){
        openReqs += { openReq("", {}, src@\loc, makeClos2(src, msg)) };
    }
    
    AType _newTypeVar(Tree scope){
        ntypevar += 1;
        s = right("<ntypevar>", 10, "0");
        tv = |typevar:///<s>|;
        tvScopes[tv] = scope@\loc;
        return tvar(tv);
    }
    
    FRModel _build(){
       frm = scopeGraph();
       frm.defines = defines;
       frm.scopes = scopes;
       frm.paths = paths;
       frm.referPaths = referPaths;
       frm.uses = uses;
       
       frm.overloads = overloads;
       frm.facts = facts;
       frm.openFacts = openFacts;
       frm.openReqs = openReqs;
       frm.tvScopes = tvScopes;
       return frm; 
    }
    
    return frbuilder(_define, _use, _use_ref, _use_qual, _use_qual_ref, _addScope, _require, _fact1, _fact2, _overload, _error,  _newTypeVar, _build); 
}