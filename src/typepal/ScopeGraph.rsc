module typepal::ScopeGraph

// ScopeGraphs inspired by Kastens & Waite, Name analysis for modern languages: a general solution, SP&E, 2017

import IO;
import Set;
import List;

bool luDebug = false;

alias Key = loc;    // a syntactic range in the source code

data Exception
    = NoKey()
    ;

// IdRole: the various (language-specific) roles identifiers can play.
// Initially IdRole is empty but is extended in a language-specific module

data IdRole;

// PathLabel: the various (language-specific) labelled semantic paths
// between program parts
// Initially PathLabel is empty but may be extended in a language-specific module

data PathLabel;
    
// Applied occurrence (use) of id for given IdRoles
// IdRoles are used to fold multiple scopeGraphs into one 
// (e.g., one for class and package names, one for variable names etc.)
data Use(int defLine = 0) 
    = use(str id, Key occ, Key scope, set[IdRole] idRoles)
    | useq(list[str] ids, Key occ, Key scope, set[IdRole] idRoles, set[IdRole] qualifierRoles)
    ;
alias Uses = list[Use];

str getId(Use u) = u has id ? u.id : intercalate(".", u.ids);

data ReferPath
    = refer(Use use, PathLabel pathLabel)
    ;

alias ReferPaths = set[ReferPath];

// Language-specific auxiliary associated with a name definition
// Extended in a language-specific module

data DefInfo
    = noDefInfo()
    ;

default FRModel finalizeFRModel(FRModel frm) = frm;

// A single definition, in range, id is bound in a IdRole to defined
alias Define  = tuple[Key scope, str id, IdRole idRole, Key defined, DefInfo defInfo];
alias Defines = set[Define];                                 // All definitions
alias Scopes  = map[Key inner, Key outer];                   // Syntactic containment
alias Paths   = rel[Key from, PathLabel pathLabel, Key to];  // Semantic containment path

data FRModel (
    Defines defines = {},
    Scopes scopes = (),
    Paths paths = {}, 
    ReferPaths referPaths = {},
    Uses uses = []
)   = frModel()
    ;

void printFRModel(FRModel frm){
    println("FRModel(");
    println("  defines = {");
    for(Define d <- frm.defines){
        println("    \<<d.scope>, <d.id>, <d.idRole>, <d.defined>\>"); 
    }
    println("  },");
    println("  parents = (");
    for(Key inner <- frm.scopes){
        println("    <inner>: <frm.scopes[inner]>");
    }
    println("  ),");
    println("  paths = {");
    for(<Key from, PathLabel label, Key to> <- frm.paths){
        println("    \<<from>, <label>, <to>\>");
    }
    println("  },");
    println("  referPath = {");
    for(c <- frm.referPaths){
        println("    <c>");
    }
    println("  },");
    //iprintln(frm.uses);
    println("  uses = [");
    for(Use u <- frm.uses){
        print("    use(<u.ids? ? u.ids : u.id>, <u.occ>, <u.scope>, <u.idRoles>, <u.qualifierRoles? ? u.qualifierRoles : "">, <u.defLine>)");
    }
    println("  ]");
    println(");");
}

// Retrieve a unique binding for use in given syntactic scope
private Key bind(FRModel frm, Key scope, str id, set[IdRole] idRoles){
    defs = frm.defines[scope, id, idRoles];
    
    if(luDebug) println("\tbind: <scope>, <id>, <idRoles>
                       '\tbind: <defs>");
    
    if({<Key res, DefInfo dinfo>} := defs){
        if(luDebug) println("\tbind: <scope>, <id>, <idRoles> =\> <res>");
        return res;
    }
    if(size(defs) > 1){
       println("\tbind: <scope>, <id> is ambiguous: <defs>");
    }
    
    if(luDebug) println("\t---- bind, NoKey: <scope>, <id>");
    throw NoKey();
}

// Lookup use in given syntactic scope
private Key lookupScope(FRModel frm, Key scope, Use use){
    if(luDebug) println("\tlookupScope: <scope>, <use>");
    def = bind(frm, scope, use.id, use.idRoles);
    if(isAcceptableSimple(frm, def, use) == acceptBinding()){
       if(luDebug) println("\tlookupScope, <scope>. <use> ==\> <def>");
       return def;
    }
    if(luDebug) println("\tlookupScope, NoKey: <use>");
    throw NoKey();
}

// Find all (semantics induced) bindings for use in given syntactic scope via pathLabel
private list[Key] lookupPaths(FRModel frm, Key scope, Use use, PathLabel pathLabel){
    if(luDebug) println("\tlookupPaths: <scope>, <use>, <pathLabel>");
    res = 
      for(<scope, pathLabel, Key parent> <- frm.paths){
        try {
            def = lookupScope(frm, parent, use);
            switch(isAcceptablePath(frm, def, use, pathLabel)){
            case acceptBinding():
               append def;
             case ignoreContinue():
                  continue; 
             case ignoreSkipPath():
                  break; 
            }
        } catch NoKey():
            scope = parent;
    }
    println("\t---- lookupPaths: <scope>, <use>, <pathLabel> ==\> <res>");
    return res;
}

// Get all pathLabels and remember them
@memo 
private set[PathLabel] pathLabels(FRModel frm){
    return {pl | /PathLabel pl := frm};
    //return frm.paths.pathLabel;
}

// Lookup use in syntactic scope and via all semantic paths
private Key lookupQual(FRModel frm, Key scope, Use u){
     try 
        return lookupScope(frm, scope, u);
    catch NoKey(): {
        
        if(luDebug) println("\tlookupQual: loop over <pathLabels(frm)>");
        nextPath:
        for(PathLabel pathLabel <- pathLabels(frm)){
           candidates = lookupPaths(frm, scope, u, pathLabel);
           if(size(candidates) == 1){
              return candidates[0];
           }
           for(Key candidate <- candidates){
               switch(isAcceptableSimple(frm, candidate, u)){
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
    if(luDebug) println("\t---- lookupQual, NoKey: <u>");
    throw NoKey();
}

// Lookup use in syntactic scope and via all semantic paths,
// recur to syntactic parent until found
private Key lookupNest(FRModel frm, Key scope, Use u){
    if(luDebug)println("\tlookupNest: <scope>, <u>");
    try 
        return lookupQual(frm, scope, u);
    catch NoKey(): {
        if(frm.scopes[scope] ?){
           parent = frm.scopes[scope];
           if(luDebug)println("\tlookupNest: <scope>, <u> move up to <parent>");
           return lookupNest(frm, parent, u);
        }
        if(luDebug) println("\t---- lookupNest, NoKey: <u>");
        throw NoKey();
    }
}

public Key lookup(FRModel frm, Use u){
    scope = u.scope;
    if(luDebug) println("lookup: <u>");
    if(!(u has qualifierRoles)){
       res = lookupNest(frm, scope, u);
       if(isAcceptableSimple(frm, res, u) == acceptBinding()){
          if(luDebug) println("lookup: <u> ==\> <res>");
          return res;
       }
    } else {
       startScope = scope;
       while(true){
          scope = startScope;
           for(id <- u.ids[0..-1]){ 
               println("lookup, search for <id>");
               scope = lookupNest(frm, scope, use(id, u.occ, scope, u.qualifierRoles));
            }
       
            try {
                res = lookupNest(frm, scope, use(u.ids[-1], u.occ, scope, u.idRoles));
                if(isAcceptableQualified(frm, res, u) == acceptBinding()){
                   if(luDebug) println("lookup: <u> ==\> <res>");
                   return res;
                }
            } catch NoKey(): {
                  if(frm.scopes[startScope]?){
                     startScope = frm.scopes[startScope];
                     if(luDebug)println("^^^^ lookup move to scope <startScope>");
                  } else {
                     throw NoKey();
                  }
            }
        }
     }
     if(luDebug) println("---- lookup, NoKey: <u>");
     throw NoKey();
}

// Language-specific acceptance in case of multiple outcomes
data Accept 
    = acceptBinding()
    | ignoreContinue()
    | ignoreSkipPath()
    ;

default Accept isAcceptableSimple(FRModel frm, Key candidate, Use use) = acceptBinding();

default Accept isAcceptablePath(FRModel frm, Key candidate, Use use, PathLabel pathLabel) = acceptBinding();

default Accept isAcceptableQualified(FRModel frm, Key candidate, Use use) = acceptBinding();

default bool checkPaths(FRModel frm, Key from, Key to, PathLabel pathLabel, bool(FRModel,Key) pred) {
    current = from;
    path = [from];
    do {
        if({def} := frm.paths[current, pathLabel]){
           path += [def];
           current = def; 
        } else {
            throw "isAcceptablePath: <current>, <use>";
        }
    } while(current != to);
    return all(p <- path, pred(frm, p));
}

bool existsPath(FRModel frm, Key from, Key to, PathLabel pathLabel){
    return <from, to> in frm.paths<1,0,2>[pathLabel]*;
}