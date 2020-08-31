module analysis::typepal::ConfigurableScopeGraph

extend analysis::typepal::AType;
extend analysis::typepal::Exception;

import IO;
import Set;
import Map;
import String;
extend ParseTree;

syntax ANONYMOUS_OCCURRENCE = "anonymous_occurence";
public loc anonymousOccurrence = ([ANONYMOUS_OCCURRENCE] "anonymous_occurence")@\loc;

AType defaultGetMinAType(){
    throw TypePalUsage("`getMinAType()` called but is not specified in TypePalConfig");
}

AType defaultGetMaxAType(){
    throw TypePalUsage("`getMaxAType()` called but is not specified in TypePalConfig");
}

AType defaultGetLub(AType atype1, AType atype2){
    throw TypePalUsage("`lub(<atype1>, <atype2>)` called but `getLub` is not specified in TypePalConfig");
}

bool defaultIsSubType(AType atype1, AType atype2) {
    throw TypePalUsage("`subtype(<atype1>, <atype2>)` called but `isSubType` is not specified in TypePalConfig");
}

bool defaultMayOverload (set[loc] _, map[loc, Define] _) {
    return false;
}

 AType defaultInstantiateTypeParameters(Tree _, AType def, AType ins, AType act, Solver _){ 
   throw TypePalUsage("`instantiateTypeParameters(<prettyAType(def)>, <prettyAType(ins)>, <prettyAType(act)>)` called but is not specified in TypePalConfig");
}

tuple[list[str] typeNames, set[IdRole] idRoles] defaultGetTypeNamesAndRole(AType _){
    throw TypePalUsage("`useViaType` used without definition of `getTypeNamesAndRole`");
}

AType defaultGetTypeInNamelessType(AType _, Tree _, loc _, Solver _){
    throw TypePalUsage("`useViaType` used without definition of `getTypeInNamelessType`");
}

AType defaultGetTypeInTypeFromDefine(Define _, str _, set[IdRole] _, Solver _) {
    throw NoBinding();
}   
  
str defaultUnescapeName(str s) { return replaceAll(s, "\\", ""); }

bool defaultReportUnused (loc _, TModel _) {
    return false;
}

// Extends TypePalConfig defined in analysis::typepal::ScopeGraph

data TypePalConfig(       
        Accept (loc def, Use use, Solver s) isAcceptableSimple     
            = defaultIsAcceptableSimple,
        Accept (loc def, Use use, Solver s) isAcceptableQualified  
            = defaultIsAcceptableQualified,
        Accept (loc defScope, loc def, Use use, PathRole pathRole, Solver s) isAcceptablePath         
            = defaultIsAcceptablePath
        );

data TypePalConfig(
        bool verbose               = false,
        bool logTime               = false,
        bool logSolverSteps        = false,
        bool logSolverIterations   = false,
        bool logAttempts           = false,
        bool logTModel             = false,
        bool validateConstraints   = true,
    
        AType() getMinAType                                         
            = AType (){  throw TypePalUsage("`getMinAType()` called but is not specified in TypePalConfig"); },
            
        AType() getMaxAType
            = AType (){ throw TypePalUsage("`getMaxAType()` called but is not specified in TypePalConfig"); },
            
        bool (AType t1, AType t2) isSubType                         
            = bool (AType atype1, AType atype2) { throw TypePalUsage("`subtype(<atype1>, <atype2>)` called but `isSubType` is not specified in TypePalConfig"); },
        
        AType (AType t1, AType t2) getLub                           
            = AType (AType atype1, AType atype2){ throw TypePalUsage("`lub(<atype1>, <atype2>)` called but `getLub` is not specified in TypePalConfig"); },        
        
        bool (set[loc] defs, map[loc, Define] defines) mayOverload 
            = bool (set[loc] _, map[loc, Define] _) { return false; },
            
        bool (IdRole idRole) isInferrable
            = bool(IdRole _) { return false; },
        
        str(str) unescapeName                                       
            = str (str s) { return replaceAll(s, "\\", ""); },
        
        AType (Tree selector, AType def, AType ins, AType act, Solver s) instantiateTypeParameters 
            = AType(Tree _, AType _, AType _, AType act, Solver _){ return act; },
       
        tuple[list[str] typeNames, set[IdRole] idRoles] (AType atype) getTypeNamesAndRole
            = tuple[list[str] typeNames, set[IdRole] idRoles](AType _){
                throw TypePalUsage("`useViaType` used without definition of `getTypeNamesAndRole`");
            },
            
        AType (Define containerDef, str selectorName, set[IdRole] idRolesSel, Solver s) getTypeInTypeFromDefine
            = AType (Define _, str _, set[IdRole] _, Solver _) { throw NoBinding(); },
 
        AType(AType containerType, Tree selector, loc scope, Solver s) getTypeInNamelessType
            = AType(AType _, Tree _, loc _, Solver _){
                throw TypePalUsage("`useViaType` used without definition of `getTypeInNamelessType`");
            }, 
            
        TModel(map[str,Tree] namedTrees, TModel tm) preSolver = TModel(map[str,Tree] _, TModel tm) { return tm; },    
        void (map[str,Tree] namedTrees, Solver s) postSolver  = void(map[str,Tree] _, Solver _) { return ; },
        
        bool(loc def, TModel tm) reportUnused = defaultReportUnused
    );
    

// ScopeGraphs inspired by Kastens & Waite, Name analysis for modern languages: a general solution, SP&E, 2017


//data Tree;      // workaround for bug in interpreter

   
// Language-specific acceptance in case of multiple outcomes of a lookup

data Accept 
    = acceptBinding()
    | ignoreContinue()
    | ignoreSkipPath()
    ;

// isAcceptableSimple

Accept defaultIsAcceptableSimple(loc candidate, Use use, Solver _) {
    if(wdebug) println("default isAcceptableSimple: <use.id> candidate: <candidate>");
    return acceptBinding();
}

// isAcceptablePath

Accept defaultIsAcceptablePath(loc defScope, loc def, Use use, PathRole _, Solver _) {
    if(wdebug) println("default isAcceptablePath: <use.id>, defScope: <defScope>, def <def>");
    return acceptBinding();
}

// isAcceptableQualified
Accept defaultIsAcceptableQualified(loc _, Use _, Solver _) = acceptBinding();

default bool checkPaths(TModel tm, loc from, loc to, PathRole pathRole, bool(TModel,loc) pred) {
    current = from;
    path = [from];
    do {
        if({def} := tm.paths[current, pathRole]){
           path += [def];
           current = def; 
        } else {
            throw "isAcceptablePath: <current>, <use>";
        }
    } while(current != to);
    return all(p <- path, pred(tm, p));
}

bool existsPath(TModel tm, loc from, loc to, PathRole pathRole){
    return <from, to> in tm.paths<1,0,2>[pathRole]*;
}

// The ScopeGraph structure that provides lookup operations n a TModel
data ScopeGraph
    = scopegraph(
        set[loc] (Use u) lookup
    );
    
bool wdebug = false;
    
ScopeGraph newScopeGraph(TModel tm, TypePalConfig config, Solver s){
 
    /*************************************************************************/
    /* At the moment we support "classic" scopes from the Kastens & Waite    */
    /* article and "wide" scopes as used for Rascal. We still have to settle */
    /* on the definitive version. For now only wide scopes are used.         */
    /*************************************************************************/
    
    // Retrieve a unique binding for use in given syntactic scope
    //loc bind(TModel tm, loc scope, str id, set[IdRole] idRoles){
    //    defs = tm.defines[scope, id, idRoles];
    //    
    //    if(luDebug) println("\tbind: <scope>, <id>, <idRoles>
    //                       '\tbind: <defs>");
    //    
    //    if({<loc res, DefInfo dinfo>} := defs){
    //        if(luDebug) println("\tbind: <scope>, <id>, <idRoles> =\> <res>");
    //        return res;
    //    }
    //    if(size(defs) > 1){
    //       throw AmbiguousDefinition(defs<0>);
    //    }
    //    
    //    if(luDebug) println("\t---- bind, NoBinding: <scope>, <id>");
    //    throw NoBinding();
    //}
    //
    //// Lookup use in given syntactic scope
    //private loc lookupScope(TModel tm, loc scope, Use use){
    //    if(luDebug) println("\tlookupScope: <scope>, <use>");
    //    def = bind(tm, scope, use.id, use.idRoles);
    //    if(isAcceptableSimpleFun(tm, def, use) == acceptBinding()){
    //       if(luDebug) println("\tlookupScope, <scope>. <use> ==\> <def>");
    //       return def;
    //    }
    //    if(luDebug) println("\tlookupScope, NoBinding: <use>");
    //    throw NoBinding();
    //}
    //
    //// Find all (semantics induced) bindings for use in given syntactic scope via PathRole
    //private list[loc] lookupPaths(TModel tm, loc scope, Use use, PathRole pathRole){
    //    //println("\tlookupPaths: <use.id> in scope <scope>, pathRole <pathRole>");
    //    res = 
    //      for(<scope, pathRole, loc parent> <- tm.paths){
    //        try {
    //            loc def = lookupScope(tm, parent, use);
    //            switch(isAcceptablePathFun(tm, parent, def, use, pathRole)){
    //            case acceptBinding():
    //               append def;
    //             case ignoreContinue():
    //                  continue; 
    //             case ignoreSkipPath():
    //                  break; 
    //            }
    //        } catch NoBinding():
    //            scope = parent;
    //    }
    //    if(luDebug)println("\t---- lookupPaths: <scope>, <use>, <pathRole> ==\> <res>");
    //    return res;
    //}
    //
    //// Lookup use in syntactic scope and via all semantic paths
    //private loc lookupQual(TModel tm, loc scope, Use u){
    //     try 
    //        return lookupScope(tm, scope, u);
    //    catch NoBinding(): {
    //        
    //        if(luDebug) println("\tlookupQual: loop over <pathRoles(tm)>");
    //        nextPath:
    //        for(PathRole pathRole <- pathRoles(tm)){
    //           candidates = lookupPaths(tm, scope, u, pathRole);
    //           if(size(candidates) == 1){
    //              return candidates[0];
    //           }
    //           for(loc candidate <- candidates){
    //               switch(isAcceptableSimpleFun(tm, candidate, u)){
    //               case acceptBinding():
    //                  return candidate;
    //               case ignoreContinue():
    //                  continue;
    //               case ignoreSkipPath():
    //                  continue nextPath;
    //               }
    //            }
    //        }
    //    }
    //    if(luDebug) println("\t---- lookupQual, NoBinding: <u>");
    //    throw NoBinding();
    //}
    //
    //// Lookup use in syntactic scope and via all semantic paths,
    //// recur to syntactic parent until found
    //private loc lookupNest(TModel tm, loc scope, Use u){
    //    if(luDebug)println("\tlookupNest: <scope>, <u>");
    //    try 
    //        return lookupQual(tm, scope, u);
    //    catch NoBinding(): {
    //        if(tm.scopes[scope] ? && tm.scopes[scope] != scope){
    //           parent = tm.scopes[scope];
    //           if(luDebug)println("\tlookupNest: <scope>, <u> move up to <parent>");
    //           return lookupNest(tm, parent, u);
    //        }
    //        if(luDebug) println("\t---- lookupNest, NoBinding: <u>");
    //        throw NoBinding();
    //    }
    //}
    //
    //public loc lookup1(TModel tm, Use u){
    //    scope = u.scope;
    //    if(luDebug) println("lookup: <u>");
    //    if(!(u has qualifierRoles)){
    //       res = lookupNest(tm, scope, u);
    //       if(isAcceptableSimpleFun(tm, res, u) == acceptBinding()){
    //          if(luDebug) println("lookup: <u> ==\> <res>");
    //          return res;
    //       }
    //    } else {
    //       startScope = scope;
    //       while(true){
    //          scope = startScope;
    //           for(id <- u.ids[0..-1]){ 
    //               if(luDebug)println("lookup, search for <id>");
    //               scope = lookupNest(tm, scope, use(id, u.occ, scope, u.qualifierRoles));
    //            }
    //       
    //            try {
    //                res = lookupNest(tm, scope, use(u.ids[-1], u.occ, scope, u.idRoles));
    //                if(isAcceptableQualifiedFun(tm, res, u) == acceptBinding()){
    //                   if(luDebug) println("lookup: <u> ==\> <res>");
    //                   return res;
    //                }
    //            } catch NoBinding(): {
    //                  if(tm.scopes[startScope]?){
    //                     startScope = tm.scopes[startScope];
    //                     if(luDebug)println("^^^^ lookup move to scope <startScope>");
    //                  } else {
    //                     throw NoBinding();
    //                  }
    //            }
    //        }
    //     }
    //     if(luDebug) println("---- lookup, NoBinding: <u>");
    //     throw NoBinding();
    //}
    //
    //public set[loc] lookup(TModel tm, Use u){
    //    try {
    //        return {lookup1(tm, u)};
    //    } catch AmbiguousDefinition(set[loc] definitions):
    //        return definitions;
    //}
    
    /************************************************************************************/
    /* "wide" scopes were designed to suit Rascal's scope model where names from        */
    /* imported modules co-exist with names declared in the current module.             */
    /* lookupWide returns all definitions in the current syntactic scope (or its        */
    /* parents) and definitions that can be reached in a single step via semantic links */                             
    /************************************************************************************/
    
    //@memo
    // Retrieve all bindings for use in given syntactic scope
    private set[loc] bindWide(loc scope, str id, set[IdRole] idRoles){
        preDefs = (tm.definesMap[scope] ? ())[id] ? {};
        
        if(isEmpty(preDefs) || isEmpty(preDefs<0> & idRoles)) return {};
        return preDefs<1>;
    }
    
    // Lookup use in the given syntactic scope
    private set[loc] lookupScopeWide(loc scope, Use use){
        //if(wdebug) println("\tlookupScopeWide: <use.id> in scope <scope>");
    
        return {def | def <-  bindWide(scope, use.id, use.idRoles), isAcceptableSimpleFun(def, use, the_solver) == acceptBinding()}; 
    }
    
    //@memo
    // Find all (semantics induced, one-level) bindings for use in given syntactic scope via PathRole
    private set[loc] lookupPathsWide(loc scope, Use use, PathRole pathRole){
        //if(wdebug) println("\tlookupPathsWide: <use.id> in scope <scope>, role <pathRole>\n<for(p <- tm.paths){>\t---- <p>\n<}>");
        res = {};
        
        seenParents = {};
        solve(res, scope) {
        next_path:
            for(<scope, pathRole, loc parent> <- paths, parent notin seenParents){
                seenParents += parent;
                //if(wdebug) println("\tlookupPathsWide: scope: <scope>, trying semantic path to: <parent>");
                
                for(loc def <- lookupScopeWide(parent, use)){
                    switch(isAcceptablePathFun(parent, def, use, pathRole, the_solver)){
                    case acceptBinding():
                       res += def;
                     case ignoreContinue():
                          continue; 
                     case ignoreSkipPath():
                          continue next_path; 
                    }
                }
            }       
        }
        //if(wdebug) println("\tlookupPathsWide: <use.id> in scope <scope>, <pathRole> ==\> <res>");
        return res;
    }
    
    // Lookup use in given syntactic scope and via all semantic paths
    private set[loc] lookupQualWide(loc scope, Use u){
        //if(wdebug) println("\tlookupQualWide: <u.id> in scope <scope>");
      
        res = lookupScopeWide(scope, u);
        //if(wdebug) println("\tlookupQualWide: <u.id> in scope <scope>, after lookupScopeWide:\n<for(r <- res){>\t--\> <r><}>");
       
        //if(wdebug) println("\tlookupQualWide: <res>, loop over <pathRoles(tm)>");
        nextPath:
        for(PathRole pathRole <- pathRoles){
           candidates = lookupPathsWide(scope, u, pathRole);
           //if(wdebug) println("\tlookupQualWide: candidates: <candidates>");
           for(loc candidate <- candidates){
               switch(isAcceptableSimpleFun(candidate, u, the_solver)){
               case acceptBinding():
                  res += candidate;
               case ignoreContinue():
                  continue;
               case ignoreSkipPath():
                  continue nextPath;
               }
            }
        }
        
        return res;
    }
    
    // Lookup use in syntactic scope and via all semantic paths,
    // recur to syntactic parent until found
    private set[loc] lookupNestWide(loc scope, Use u){
        //if(wdebug) println("\tlookupNestWide: <u.id> in scope <scope>");
       
        res = lookupQualWide(scope, u);
        //if(wdebug) println("\tlookupNestWide: <u.id> in scope <scope> found:\n<for(r <- res){>\t==\> <r><}>");
        if(!isEmpty(res)) return res; // <<<
    
        if(tm.scopes[scope] ?){
          if(scope == tm.scopes[scope]) { println("Identical scope in lookupNestWide: <scope>"); return res; }
           parent = tm.scopes[scope];
           //if(wdebug) println("\tlookupNestWide: <u.id> in scope <scope> move up to <parent>");
           res += lookupNestWide(parent, u);
        }
      
        return res;
    }
    
    Paths paths = s.getPaths();
    set[PathRole] pathRoles = paths.pathRole;
    
    public set[loc] lookupWide(Use u){
    
        // Update current paths and pathRoles
        current_paths = s.getPaths();
        if(current_paths != paths){
            paths = current_paths;
            pathRoles = paths.pathRole;
        }
        
        scope = u.scope;
     
        //if(wdebug) println("lookupWide: <u>");
        if(!(u has qualifierRoles)){
           defs = {def | loc def <- lookupNestWide(scope, u), isAcceptableSimpleFun(def, u, the_solver) == acceptBinding()};
           //if(wdebug) println("lookupWide: <u> returns:\n<for(d <- defs){>\t==\> <d><}>");
           if(isEmpty(defs)) throw NoBinding(); else return defs;
        } else {
           startScope = scope;
           while(true){
               qscopes = {};
               for(str id <- u.ids[0..-1]){ 
                   //if(wdebug) println("lookup, search for <id>"); 
                   qscopes = lookupNestWide(scope, use(id, u.occ, scope, u.qualifierRoles));
                   if(isEmpty(qscopes)) throw NoBinding();
                }
    
                defs = {};
                for(loc qscope <- qscopes){
                    scopeLookups = lookupNestWide(qscope, use(u.ids[-1], u.occ, qscope, u.idRoles));
                    defs += { def | def <- scopeLookups, isAcceptableQualifiedFun(def, u, the_solver) == acceptBinding()};            
                }
                if(!isEmpty(defs)){
                    //if(wdebug) println("lookupWide: <u> returns:\n<for(d <- defs){>\t==\> <d><}>");
                    return defs;
                }
       
                if(tm.scopes[startScope]?){
                     startScope = tm.scopes[startScope];
                     //if(wdebug) println("^^^^ lookup move to scope <startScope>");
                } else {
                     allScopes = domain(tm.scopes) + range(tm.scopes);
                     for(str id <- u.ids[0..-1]){ 
                        qscopes = lookupNestWide(scope, use(id, u.occ, scope, u.qualifierRoles));
                        for(loc qscope <- qscopes){
                            if(qscope notin allScopes){
                                throw TypePalUsage("Definition of qualifier `<id>` is unknown as scope, check its definition", [qscope]);
                            }
                        }
                     }
                     throw NoBinding();
                }
            }
         }
         throw NoBinding();
    }
    
    // Initialize the ScopeGraph context
    
    Solver the_solver = s;
    
    Accept (loc def, Use use, Solver s) isAcceptableSimpleFun     = config.isAcceptableSimple;
    Accept (loc def, Use use, Solver s) isAcceptableQualifiedFun  = config.isAcceptableQualified;
    Accept (loc defScope, loc def, Use use, PathRole pathRole, Solver s) isAcceptablePathFun 
                                                                  = config.isAcceptablePath;
       
    return scopegraph(
            lookupWide
        );
}