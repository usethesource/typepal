module ScopeGraph

// ScopeGraphs inspired by Kastens & Waite, Name analysis for modern languages: a general solution, SP&E, 2017

import IO;
import Set;
import List;

bool debug = false;

alias Idn = str;    // an identifier

alias Key = loc;    // a syntactic range in the source code
Key noKey = |nokey:///|;

// Various kinds of (language-specific) identifier declarations
// Extended in language-specific module

data IdRole
    = noIdRole()
    ;

// Various kinds of (language-specific) path labels
// Extended in language-specific module

data PathLabel
    = noPathLabel()
    ;
    
// Applied occurrence (use) of id for given IdRoles
// IdRoles are used to fold multiple scopeGraphs into one 
// (e.g., one for class and package names, one for variable names etc.)
data Use(int defLine = 0) 
    = use(Idn id, Key occ, Key scope, set[IdRole] idRoles)
    | use(list[Idn] ids, Key occ, Key scope, set[IdRole] idRoles, set[IdRole] qualifierRoles)
    ;
alias Uses = list[Use];

data ReferPath
    = refer(Use use, PathLabel pathLabel)
    ;

alias ReferPaths = set[ReferPath];

// Language-specific auxiliary data
// Extended in language-specific module

data DefInfo
    = noDefInfo()
    ;

default ScopeGraph finalizeScopeGraph(ScopeGraph sg) = sg;

// A single definition, in range, id is bound in a IdRole to defined
alias Define  = tuple[Key scope, Idn id, IdRole idRole, Key defined, DefInfo defInfo];
alias Defines = set[Define];                                 // All definitions
alias Scopes  = map[Key inner, Key outer];                   // Syntactic containment
alias Paths   = rel[Key from, PathLabel pathLabel, Key to];  // Semantic containment path

data ScopeGraph (
    Defines defines = {},
    Scopes scopes = (),
    Paths paths = {}, 
    ReferPaths referPaths = {},
    Uses uses = [])
    
    = scopeGraph()
    ;

void printScopeGraph(ScopeGraph sg){
    println("scopeGraph(");
    println("  defines = {");
    for(Define d <- sg.defines){
        println("    \<<d.scope>, <d.id>, <d.idRole>, <d.defined>\>"); 
    }
    println("  },");
    println("  parents = (");
    for(Key inner <- sg.scopes){
        println("    <inner>: <sg.scopes[inner]>");
    }
    println("  ),");
    println("  paths = {");
    for(<Key from, PathLabel label, Key to> <- sg.paths){
        println("    \<<from>, <label>, <to>\>");
    }
    println("  },");
    println("  referPath = {");
    for(c <- sg.referPaths){
        println("    <c>");
    }
    println("  },");
    println("  uses = [");
    for(u <- sg.uses){
        print("    use(");
        if(u has qualifierRoles){
            println("<u.ids>, <u.occ>, <u.scope>, <u.idRoles>, <u.qualifierRoles>, <u.defLine>)");
        } else {
           println("<u.id>, <u.occ>, <u.scope>, <u.idRoles>, <u.defLine>)");
        }
    }
    println("  ]");
    println(");");
}

// Retrieve a unique binding for use in given syntactic context
private Key bind(ScopeGraph sg, Key context, Idn id, set[IdRole] idRoles){
    defs = sg.defines[context, id, idRoles];
    
    if({<Key res, DefInfo dinfo>} := defs){
        if(debug) println("bind: <context>, <id>, <idRoles> =\> <res>");
        return res;
    }
    if(size(defs) > 1){
       println("bind: <context>, <id> is ambiguous: <defs>");
    }
    //if(debug)println("bind: <context>, <id>, <bindingLabels> =\> noKey");
    throw noKey;
}

// Lookup use in given syntactic context
private Key lookupScope(ScopeGraph sg, Key context, Use u){
    if(debug) println("lookupScope: <context>, <u>");
    if(!(u has qualifierRoles)){
       def = bind(sg, context, u.id, u.idRoles);
       if(isAcceptableSimple(sg, def, u) == acceptBinding()){
          return def;
       }
    } 
    throw noKey;
}

// Find all (semantics induced) bindings for use in given syntactic context via pathLabel
private list[Key] lookupPaths(ScopeGraph sg, Key context, Use use, PathLabel pathLabel){
    return 
      for(<context, pathLabel, Key parent> <- sg.paths){
        try {
            def = lookupScope(sg, parent, use);
            switch(isAcceptablePath(sg, def, use, pathLabel)){
            case acceptBinding():
               append def;
             case ignoreContinue():
                  continue; 
             case ignoreSkipPath():
                  break; 
            }
        } catch noKey:
            context = parent;
    }
}

// Get all pathLabels and remember them
@memo 
private set[PathLabel] pathLabels(ScopeGraph sg){
    return sg.paths.pathLabel;
}

// Lookup use in syntactic context and via all semantic paths
private Key lookupQual(ScopeGraph sg, Key context, Use use){
     try 
        return lookupScope(sg, context, use);
    catch noKey: {
        nextPath:
        for(PathLabel pathLabel <- pathLabels(sg)){
           candidates = lookupPaths(sg, context, use, pathLabel);
           if(size(candidates) == 1){
              return candidates[0];
           }
           for(Key candidate <- candidates){
               switch(isAcceptableSimple(sg, candidate, use)){
               case acceptBinding():
                  return candidate;
               case ignoreContinue():
                  continue;
               case ignoreSkipPath():
                  continue nextPath;
               }
            }
        }
    }
    throw noKey;
}

// Lookup use in syntactic context and via all semantic paths,
// recur to syntactic parent until found
private Key lookupNest(ScopeGraph sg, Key context, Use use){
    if(debug)println("lookupNest: <context>, <use>");
    try 
        return lookupQual(sg, context, use);
    catch noKey: {
        if(sg.scopes[context] ?){
           parent = sg.scopes[context] ? noKey;
           if(debug)println("lookupNest: <context>, <use> move up to <parent>");
           return lookupNest(sg, parent, use);
        }
        throw noKey;
    }
}

public Key lookup(ScopeGraph sg, Key context, Use a){
    if(debug) println("lookup: <context>, <a>");
    if(!(a has qualifierRoles)){
       res = lookupNest(sg, context, a);
       if(isAcceptableSimple(sg, res, a) == acceptBinding()){
          return res;
       }
    } else {
    
       for(id <- a.ids[0..-1]){ 
           context = lookupNest(sg, context, use(id, a.occ, context, a.qualifierRoles));
        }
        res = lookupNest(sg, context, use(a.ids[-1], a.occ, context, a.idRoles));
        if(isAcceptableQualified(sg, res, a) == acceptBinding()){
           return res;
        }
     }
     throw noKey;
}

// Language-specific acceptance in case of multiple outcomes
data Accept 
    = acceptBinding()
    | ignoreContinue()
    | ignoreSkipPath()
    ;

default Accept isAcceptableSimple(ScopeGraph sg, Key candidate, Use use) = acceptBinding();

default Accept isAcceptablePath(ScopeGraph sg, Key candidate, Use use, PathLabel pathLabel) = acceptBinding();

default Accept isAcceptableQualified(ScopeGraph sg, Key candidate, Use use) = acceptBinding();

default bool checkPaths(ScopeGraph sg, Key from, Key to, PathLabel pathLabel, bool(ScopeGraph,Key) pred) {
    current = from;
    path = [from];
    do {
        if({def} := sg.paths[current, pathLabel]){
           path += [def];
           current = def; 
        } else {
            throw "isAcceptablePath: <current>, <use>";
        }
    } while(current != to);
    return all(p <- path, pred(sg, p));
}