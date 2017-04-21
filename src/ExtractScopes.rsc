module ExtractScopes

import IO;
extend ScopeGraph;
import String;
import ParseTree;
 
data SGBuilder =
    sgbuilder(
        void (Key parent, Idn id, IdRole idRole, Key root, DefFact fact) define,
        void (Idn id, Key occ, Key parent, set[IdRole] idRoles, int defLine) use,
        void (Idn id, Key occ, Key parent, set[IdRole] idRoles, PathLabel pathLabel, int defLine) use_ref,
        void (list[Idn] ids, Key occ, Key parent, set[IdRole] idRoles, set[IdRole] qualifierRoles, int defLine) use_qual,
        void (list[Idn] ids, Key occ, Key parent, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel, int defLine) use_qual_ref,   
        void (Key inner, Key outer) addScope,
        ScopeGraph () build
    );
   
SGBuilder scopeGraphBuilder(){
    Defines defines = {};
    Scopes scopes = ();
    Paths paths = {};
    ReferPaths referPaths = {};
    Uses uses = [];
    
    void _define(Key parent, Idn id, IdRole idRole, Key d, DefFact fact){
        defines += {<parent, id, idRole, d, fact>};
    }
       
    void _use(Idn id, Key occ, Key parent, set[IdRole] idRoles, int defLine) {
        uses += [use(id, occ, parent, idRoles, defLine=defLine)];
    }
    
    void _use_ref(Idn id, Key occ, Key parent, set[IdRole] idRoles, PathLabel pathLabel, int defLine) {
        u = use(id, occ, parent, idRoles, defLine=defLine);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _use_qual(list[Idn] ids, Key occ, Key parent, set[IdRole] idRoles, set[IdRole] qualifierRoles, int defLine){
        uses += [use(ids, occ, parent, idRoles, qualifierRoles, defLine=defLine)];
    }
     void _use_qual_ref(list[Idn] ids, Key occ, Key parent, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathLabel pathLabel, int defLine){
        u = use(ids, occ, parent, idRoles, qualifierRoles, defLine=defLine);
        uses += [u];
        referPaths += {refer(u, pathLabel)};
    }
    
    void _addScope(Key inner, Key outer) { if(inner != outer) scopes[inner] = outer; }
    
    ScopeGraph _build() {
        sg = scopeGraph();
        sg.defines = defines;
        sg.scopes = scopes;
        sg.paths = paths;
        sg.referPaths = referPaths;
        sg.uses = uses;
        return finalizeScopeGraph(sg);
    }
    return sgbuilder(_define, _use, _use_ref, _use_qual, _use_qual_ref, _addScope, _build);
}

default Key define(str kind, &T sg, Key parent, Tree root) {
    return parent;
}

default void use(str kind, &T sg, Key parent, Tree root){
    throw "Use on <root>";
}

tuple[bool,str] isDef(appl(p:prod(_, _, {_*, \tag("def"(str s))}), _)) = <true, s[1 .. -1]>;
default tuple[bool,str] isDef(Tree _) = <false, "">;

tuple[bool,str] isUse(appl(p:prod(_, _, {_*, \tag("use"(str s))}), _)) = <true, s[1 .. -1]>;
default tuple[bool,str] isUse(Tree _) = <false, "">;
   
ScopeGraph extractScopes(Tree root){
    sgb = scopeGraphBuilder();
    extract2(root, root@\loc, sgb);
    sg = sgb.build();
    if(debug) printScopeGraph(sg);
    int n = 0;
    while(!isEmpty(sg.referPaths) && n < 3){
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

void extract2(currentTree: appl(Production prod, list[Tree] args), Key currentScope, SGBuilder sg){  
   if(<true, kind> := isDef(currentTree)){
      newScope = define(kind, sg, currentScope, currentTree);
      sg.addScope(newScope, currentScope);
      for(Tree arg <- args){
          extract2(arg, newScope, sg);
      }
   } else if(<true, kind> := isUse(currentTree)){
      use(kind, sg, currentScope, currentTree);
   } else { 
      for(Tree arg <- args){
         extract2(arg, currentScope, sg);
      }
   }
}

default SGBuilder extract2(Tree root, Key currentScope, SGBuilder sg) = sg;

tuple[bool, loc] testLookup(ScopeGraph sg, Use u, int defLine){
    try {
        def = lookup(sg, u.scope, u);
        return <def.begin.line == defLine, def>;
    } catch noKey: {
        return <defLine == 0, noKey>;
    }
} 

bool runTests(Tree ps){
    sg = extractScopes(ps);
    if(debug) printScopeGraph(sg);
    testResults = true;
    for(u <- sg.uses) {
        <result, def> = testLookup(sg, u, u.defLine);
        testResults = testResults && result;
        println("<u.occ.begin.line>: <u has id ? "<u.id>" : "<u.ids>">^<u.defLine>: <result> <result ? "" : "<def>">");
    }
    return testResults;
}
