module ExtractScopesAndConstraints

import ParseTree;
import String;
extend ScopeGraph;

data DefInfo
    = defInfo(AType tp)
    ;
    
data AType
    = typeof(loc other)                  // type dependencey on other source code fragment
    | tvar(loc name)                    // type variable
    ;

default str AType2String(AType tp) = "`<tp>`";

// Abstract type predicates

data ATypePred
    = match(AType pattern, AType subject, ErrorHandler onError)
    | equal(AType left, AType right, ErrorHandler onError)
    | fact(loc src, AType tp)
    ;

data ErrorHandler
    = onError(loc where, str msg)
    ;
   
ErrorHandler onError(Tree t, str msg) = onError(t@\loc, msg);

data Fact
    = openFact(set[loc] dependsOn, set[loc] dependsOnTV, loc src, AType tp)
    ;

data Requirement
    = require(str name, loc src, list[ATypePred] preds)
    | openReq(str name, set[loc] dependsOn, set[loc] dependsOnTV, loc src, list[ATypePred] preds)
    ;
     
data Overload
    = overload(str name, loc src, list[loc] args, 
               list[tuple[list[AType] argTypes, AType resType]] alternatives, 
               ErrorHandler onError)
    ;

ATypePred fact(Tree t, AType tp) = fact(t@\loc, tp);

bool isTypeVariable(loc tv) = tv.scheme == "typevar"; 

int maxLocalTypeVars = 100;
loc localTypeVars = |typevar:///0000000100|;

bool isLocalTypeVar(loc tv) = tv.scheme == "typevar" && tv < localTypeVars;

bool isGlobalTypeVar(loc tv) = tv.scheme == "typevar" && tv >= localTypeVars;

AType tau(int n) = tvar(|typevar:///<right("<n>", 10, "0")>|);
 
AType typeof(Tree tree) = typeof(tree@\loc);

tuple[set[loc] deps, set[loc] typeVars] extractTypeDependencies(typeof(loc l)) = <{}, {}>;
tuple[set[loc] deps, set[loc] typeVars] extractTypeDependencies(tvar(loc l)) = <{}, {}>;
default tuple[set[loc] deps, set[loc] typeVars] extractTypeDependencies(AType tp) = <{ src | /typeof(loc src) := tp },  { src | /tvar(loc src) := tp, isGlobalTypeVar(src) } >;

tuple[set[loc] deps, set[loc] typeVars] extractTypeDependencies(ATypePred tpPred) = <{ src | /typeof(loc src) := tpPred}, { src | /tvar(loc src) := tpPred, isGlobalTypeVar(src) }>;

bool allDependenciesKnown(set[loc] deps, set[loc] tvdeps, map[loc,AType] facts)
    = (isEmpty(deps) || all(dep <- deps, facts[dep]?));// && isEmpty(tvdeps);

data ScopeGraph (
        map[loc,Overload] overloads = (),
        map[loc,AType] facts = (), 
        set[Fact] openFacts = {},
        set[Requirement] openReqs = {},
        map[loc,loc] tvScopes = ()
        );

alias TENV = ScopeGraph;

alias Key = loc;

default Tree define(Tree tree, Tree scope, SGBuilder sgb) {
    return scope;
}

default void use(Tree tree, Tree scope, SGBuilder sgb){ }

default void require(Tree tree, SGBuilder sgb) { }

default void fact(Tree tree, SGBuilder sgb) { }


ScopeGraph extractScopesAndConstraints(Tree root){
    sgb = scopeGraphBuilder();
    extract2(root, root, sgb);
    sg = sgb.build();
    if(debug) printScopeGraph(sg);
    int n = 0;
    while(!isEmpty(sg.referPaths) && n < 3){    // explain this iteration count
        n += 1;
        for(c <- sg.referPaths){
            try {
                def = lookup(sg, c.use.scope, c.use);
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

void extract2(currentTree: appl(Production prod, list[Tree] args), Tree currentScope, SGBuilder sgb){   
   use(currentTree, currentScope, sgb);
   newScope = define(currentTree, currentScope, sgb);
   sgb.addScope(newScope, currentScope);
   require(currentTree, sgb);
   
   for(Tree arg <- args){
       extract2(arg, newScope, sgb);
   }
}

default void extract2(Tree root, Tree currentScope, SGBuilder sgb) { }

data SGBuilder 
    = sgbuilder(
        void (Tree scope, Idn id, IdRole idRole, Tree root, DefInfo info) define,
        void (Tree scope, Idn id, Tree occ, set[IdRole] idRoles, int defLine) use,
        void (Tree scope, Idn id, Tree occ, set[IdRole] idRoles, PathLabel pathLabel, int defLine) use_ref,
        void (Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, int defLine) use_qual,
        void (Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel, int defLine) use_qual_ref,   
        void (Tree inner, Tree outer) addScope,
       
        void (str name, Tree src, list[ATypePred] preds) require,
        void (Tree src, AType tp) fact,
        void (str name, Tree src, list[Tree] args, list[tuple[list[AType] argTypes, AType resType]] alternatives, ErrorHandler onError) overload,
        AType (Tree scope) newTypeVar,
        TENV () build
      ); 
                           
SGBuilder scopeGraphBuilder(){

    Defines defines = {};
    Scopes scopes = ();
    Paths paths = {};
    ReferPaths referPaths = {};
    Uses uses = [];
  
    overloads = ();
    facts = ();
    openFacts = {};
    reqs = {};
    binds = ();
    openReqs = {};
    ntypevar = maxLocalTypeVars - 1;
    tvScopes = ();
    
    void _define(Tree scope, Idn id, IdRole idRole, Tree d, DefInfo info){
        defines += {<scope@\loc, id, idRole, d@\loc, info>};
    }
       
    void _use(Tree scope, Idn id, Tree occ, set[IdRole] idRoles, int defLine) {
        uses += [use(id, occ@\loc, scope@\loc, idRoles, defLine=defLine)];
    }
    
    void _use_ref(Tree scope, Idn id, Tree occ, set[IdRole] idRoles, PathLabel pathLabel, int defLine) {
        u = use(id, occ@\loc, scope@\loc, idRoles, defLine=defLine);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _use_qual(Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, int defLine){
        uses += [use(ids, occ@\loc, scope@\loc, idRoles, qualifierRoles, defLine=defLine)];
    }
     void _use_qual_ref(Tree scope, list[Idn] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel, int defLine){
        u = use(ids, occ@\loc, scope@\loc, idRoles, qualifierRoles, defLine=defLine);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _addScope(Tree inner, Tree outer) { if(inner@\loc != outer@\loc) scopes[inner@\loc] = outer@\loc; }
     
    void _require(str name, Tree src, list[ATypePred] preds){        
        deps = {};
        tvdeps = {};
        
        for(pred <- preds){
            <deps1, tvdeps1> = extractTypeDependencies(pred);
            deps += deps1;
            tvdeps += tvdeps1;
        }
        if(isEmpty(deps + tvdeps)){
           reqs += { require(name, src@\loc, preds) };
        } else {
           openReqs += { openReq(name, deps, tvdeps, src@\loc, preds) };
        }
    } 
   
    void _fact(Tree src, AType tp){
        <deps, tvdeps> = extractTypeDependencies(tp);
        //println("_fact: <src@\loc>, <tp>, <typeof(loc other) := tp>, <deps>, <tvdeps>");
        if(typeof(loc other) := tp){
           //println("add: <openFact({other}, {}, src@\loc, tp)>");
           openFacts += { openFact({other}, {}, src@\loc, tp) };
        } else if(tvar(loc tv) := tp){
           openFacts += { openFact({}, {tv}, src@\loc, tp) };
        } else if(isEmpty(deps)){
           //println("add facts[<src@\loc>] = <tp>");
           facts[src@\loc] = tp;
        } else {
           openFacts += { openFact(deps, tvdeps, src@\loc, tp) };
        }
    }
    
    void _overload(str name, Tree src, list[Tree] args, list[tuple[list[AType] argTypes, AType resType]] alternatives, ErrorHandler onError){
        overloads[src@\loc] = overload(name, src@\loc, [arg@\loc | arg <- args], alternatives, onError);
    }
    
    AType _newTypeVar(Tree scope){
        ntypevar +=1;
        s = right("<ntypevar>", 10, "0");
        tv = |typevar:///<s>|;
        tvScopes[tv] = scope@\loc;
        return tvar(tv);
    }
    
    TENV _build(){
       sg = scopeGraph();
       sg.defines = defines;
       sg.scopes = scopes;
       sg.paths = paths;
       sg.referPaths = referPaths;
       sg.uses = uses;
       
       sg.overloads = overloads;
       sg.facts = facts;
       sg.openFacts = openFacts;
       sg.openReqs = openReqs;
       sg.tvScopes = tvScopes;
       return sg; 
    }
    
    return sgbuilder(_define, _use, _use_ref, _use_qual, _use_qual_ref, _addScope, _require, _fact, _overload, _newTypeVar, _build); 
}