
@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::ConfigurableScopeGraph

/*
    A ScopeGraph is the basis for TypePal's operations. It acts as a lookup function for names.
    It is highly parameterized to reflect properties of different type systems and name binding mechanisms.

    ScopeGraphs are inspired by Kastens & Waite, Name analysis for modern languages: a general solution, SP&E, 2017
*/
extend analysis::typepal::Exception;
extend analysis::typepal::ISolver;

import IO;
import Set;
import Map;
import util::PathConfig;
import String;
extend ParseTree;
import analysis::typepal::StringSimilarity;

public loc anonymousOccurrence = |rascal-typepal:///anonymous_occurrence|(0,1,<2,3>,<2,4>);

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

str defaultNormalizeName(str s) { return replaceAll(s, "\\", ""); }

bool defaultReportUnused (loc _, TModel _) {
    return false;
}

// https://en.wikipedia.org/wiki/Uniform_Resource_Identifier#:~:text=A%20URI%20is%20composed%20from,)%2C%20and%20the%20character%20%25%20.
// gen-delims: : / ? # [ ] @
// sub-delims: ! $ & ' ( ) * + , ;
// unreserved chars: a-z A-Z 0-9 - . _ ~
// percent: %

str legalInURI = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-,_~!$\'()*+;";
public set[str] legalInURIChars = { legalInURI[i] | i <- [0..size(legalInURI)] };

str reduceToURIChars(str s){
    res = "<for(int i <- [0 .. size(s)]){><s[i] in legalInURIChars ? s[i] : "_"><}>";
    //println("reduceToURIChars(<s>) =\> <res>");
    return res;
}

loc defaultLogicalLoc(Define def, str _modelName, PathConfig _pcfg){
   return def.defined; // return original and don't create logical location
}

list[str] defaultSimilarNames(Use u, TModel tm) = similarNames(u, tm);

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

        PathConfig typepalPathConfig = pathConfig(),

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

        str(str) normalizeName
            = defaultNormalizeName,

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

        bool(loc def, TModel tm) reportUnused = defaultReportUnused,

        loc (Define def, str modelName, PathConfig pcfg) createLogicalLoc = defaultLogicalLoc,

        list[str] (Use u, TModel tm) similarNames = defaultSimilarNames,

        bool enableErrorFixes = true,

        int cutoffForNameSimilarity = 3
    );


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
        defs = tm.paths[current, pathRole]; // TODO: avoided set matching in test due to compiler issue
        if(size(defs) == 1){
           def = getFirstFrom(defs);
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

// The ScopeGraph structure that provides lookup operations in a TModel
data ScopeGraph
    = scopegraph(
        set[loc] (Use u) lookup,
        void (Solver s) setSolver
    );

bool wdebug = false;

ScopeGraph newScopeGraph(TModel tm, TypePalConfig config){

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

    public set[loc] lookupWide(Use u){

        // Update current paths and pathRoles
        current_paths =  the_solver.getPaths(); //tm.paths;
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
           btrue = true;    // TODO: hack to keep Java compiler happy
           while(btrue){
               qscopes = {};
               for(str id <- u.ids[0..-1]){
                   //if(wdebug) println("lookup, search for <id>");
                   qscopes = lookupNestWide(scope, use(id, "<u.occ>", u.occ, scope, u.qualifierRoles));
                   if(isEmpty(qscopes)) throw NoBinding();
                }

                defs = {};
                for(loc qscope <- qscopes){
                    scopeLookups = lookupNestWide(qscope, use(u.ids[-1], "<u.occ>", u.occ, qscope, u.idRoles));
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
                        qscopes = lookupNestWide(scope, use(id, "<u.occ>", u.occ, scope, u.qualifierRoles));
                        for(loc qscope <- qscopes){
                            if(qscope notin allScopes){
                                throw TypePalUsage("Scope <qscope> unknown while searching for definition of qualifier `<id>` in <intercalate("::", u.ids)> at <u.occ>", [qscope]);
                            }
                        }
                     }
                     throw NoBinding();
                }
            }
         }
         throw NoBinding();
    }

    Paths paths = {};
    set[PathRole] pathRoles = {};

    Solver the_solver = dummySolver();

    void do_setSolver(Solver s){
        the_solver = s;
        paths = the_solver.getPaths();
        pathRoles = paths.pathRole;
    }

    // Initialize the ScopeGraph context

    Accept (loc def, Use use, Solver s) isAcceptableSimpleFun     = config.isAcceptableSimple;
    Accept (loc def, Use use, Solver s) isAcceptableQualifiedFun  = config.isAcceptableQualified;
    Accept (loc defScope, loc def, Use use, PathRole pathRole, Solver s) isAcceptablePathFun
                                                                  = config.isAcceptablePath;

    return scopegraph(
            lookupWide,
            do_setSolver
        );
}