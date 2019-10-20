@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIWideT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::ScopeGraph

// ScopeGraphs inspired by Kastens & Waite, Name analysis for modern languages: a general solution, SP&E, 2017

import IO;
import Set;
import List;
import Node;
import String;

data Tree;      // workaround for bug in interpreter
data Solver;

data TypePalConfig(       
        Accept (TModel tm, loc def, Use use) isAcceptableSimple     
            = defaultIsAcceptableSimple,
        Accept (TModel tm, loc def, Use use) isAcceptableQualified  
            = defaultIsAcceptableQualified,
        Accept (TModel tm, loc defScope, loc def, Use use, PathRole pathRole) isAcceptablePath         
            = defaultIsAcceptablePath
        ) = tconfig();

private bool luDebug = false;

data Exception
    = NoBinding()
    | AmbiguousDefinition(set[loc] definitions)
    ;

// IdRole: the various (language-specific) roles identifiers can play.
// Initially IdRole is empty but is extended in a language-specific module

data IdRole
    = variableId()
    ;

str prettyRole(IdRole idRole){
    stripped1 = replaceAll(getName(idRole), "Id", "");
    return visit(stripped1) { case /<ch:[A-Z]>/ => " " + toLowerCase(ch) };
}      

// PathRole: the various (language-specific) labelled semantic paths
// between program parts
// Initially PathRole is empty but may be extended in a language-specific module

data PathRole;

// ScopeRole: the various (language-specific) roles scopes can play.
// Initially ScopeRole only provides the rootScope but is extended in a language-specific module

data ScopeRole
    = anonymousScope()
    ;
    
// Applied occurrence (use) of id for given IdRoles
// IdRoles are used to fold multiple scopeGraphs into one 
// (e.g., one for class and package names, one for variable names etc.)
data Use
    = use(str id, loc occ, loc scope, set[IdRole] idRoles)
    | useq(list[str] ids, loc occ, loc scope, set[IdRole] idRoles, set[IdRole] qualifierRoles)
    ;
alias Uses = list[Use];

str getId(Use u) = u has id ? u.id : intercalate(".", u.ids);

data ReferPath
    = referToDef(Use use, PathRole pathRole)
    | referToType(loc occ, loc scope, PathRole pathRole)
    ;

alias ReferPaths = set[ReferPath];

// Language-specific auxiliary associated with a name definition
// Extended in a language-specific module

data DefInfo
    = noDefInfo()
    ;

// A single definition: in scope, id is bound in a IdRole to defined, with DefInfo attached
alias Define  = tuple[loc scope, str id, IdRole idRole, loc defined, DefInfo defInfo];
alias Defines = set[Define];                                 // All defines
alias Scopes  = map[loc inner, loc outer];                   // Syntactic containment
alias Paths   = rel[loc from, PathRole pathRole, loc to];    // Semantic containment path

// The foundation of aTModel. Its is extended in Collector and can also be extended
// In a TypePal application

data TModel (
    Defines defines = {},
    Scopes scopes = (),
    Paths paths = {}, 
    ReferPaths referPaths = {},
    Uses uses = [],
    map[loc, map[str, rel[IdRole idRole, loc defined]]] definesMap = ()
)   = tmodel()
    ;
    
   
// Language-specific acceptance in case of multiple outcomes of a lookup

data Accept 
    = acceptBinding()
    | ignoreContinue()
    | ignoreSkipPath()
    ;

// isAcceptableSimple

Accept defaultIsAcceptableSimple(TModel tm, loc candidate, Use use) {
    if(wdebug) println("default isAcceptableSimple: <use.id> candidate: <candidate>");
    return acceptBinding();
}

//Accept (TModel tm, loc candidate, Use use) isAcceptableSimpleFun = defaultIsAcceptableSimple;

// isAcceptablePath

Accept defaultIsAcceptablePath(TModel tm, loc defScope, loc def, Use use, PathRole pathRole) {
    if(wdebug) println("default isAcceptablePath: <use.id>, defScope: <defScope>, def <def>");
    return acceptBinding();
}

// isAcceptableQualified
Accept defaultIsAcceptableQualified(TModel tm, loc candidate, Use use) = acceptBinding();

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
        set[loc] (TModel tm, Use u) lookup
    );
    
bool wdebug = false;
    
ScopeGraph newScopeGraph(TypePalConfig tc){

    // Get all pathRoles and remember them
    @memo 
    private set[PathRole] pathRoles(TModel tm){
        //return {pl | /PathRole pl := tm};
        return tm.paths.pathRole;
    }
    
    /*************************************************************************/
    /* At the moment we support "classic" scopes from the Kastens & Waite    */
    /* article and "wide" scopes as used for Rascal. We still have to settle */
    /* on the definitive version. For now only wide scopes are used.         */
    /*************************************************************************/
    
    // Retrieve a unique binding for use in given syntactic scope
    loc bind(TModel tm, loc scope, str id, set[IdRole] idRoles){
        defs = tm.defines[scope, id, idRoles];
        
        if(luDebug) println("\tbind: <scope>, <id>, <idRoles>
                           '\tbind: <defs>");
        
        if({<loc res, DefInfo dinfo>} := defs){
            if(luDebug) println("\tbind: <scope>, <id>, <idRoles> =\> <res>");
            return res;
        }
        if(size(defs) > 1){
           throw AmbiguousDefinition(defs<0>);
        }
        
        if(luDebug) println("\t---- bind, NoBinding: <scope>, <id>");
        throw NoBinding();
    }
    
    // Lookup use in given syntactic scope
    private loc lookupScope(TModel tm, loc scope, Use use){
        if(luDebug) println("\tlookupScope: <scope>, <use>");
        def = bind(tm, scope, use.id, use.idRoles);
        if(isAcceptableSimpleFun(tm, def, use) == acceptBinding()){
           if(luDebug) println("\tlookupScope, <scope>. <use> ==\> <def>");
           return def;
        }
        if(luDebug) println("\tlookupScope, NoBinding: <use>");
        throw NoBinding();
    }
    
    // Find all (semantics induced) bindings for use in given syntactic scope via PathRole
    private list[loc] lookupPaths(TModel tm, loc scope, Use use, PathRole pathRole){
        //println("\tlookupPaths: <use.id> in scope <scope>, pathRole <pathRole>");
        res = 
          for(<scope, pathRole, loc parent> <- tm.paths){
            try {
                loc def = lookupScope(tm, parent, use);
                switch(isAcceptablePathFun(tm, parent, def, use, pathRole)){
                case acceptBinding():
                   append def;
                 case ignoreContinue():
                      continue; 
                 case ignoreSkipPath():
                      break; 
                }
            } catch NoBinding():
                scope = parent;
        }
        if(luDebug)println("\t---- lookupPaths: <scope>, <use>, <pathRole> ==\> <res>");
        return res;
    }
    
    // Lookup use in syntactic scope and via all semantic paths
    private loc lookupQual(TModel tm, loc scope, Use u){
         try 
            return lookupScope(tm, scope, u);
        catch NoBinding(): {
            
            if(luDebug) println("\tlookupQual: loop over <pathRoles(tm)>");
            nextPath:
            for(PathRole pathRole <- pathRoles(tm)){
               candidates = lookupPaths(tm, scope, u, pathRole);
               if(size(candidates) == 1){
                  return candidates[0];
               }
               for(loc candidate <- candidates){
                   switch(isAcceptableSimpleFun(tm, candidate, u)){
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
        if(luDebug) println("\t---- lookupQual, NoBinding: <u>");
        throw NoBinding();
    }
    
    // Lookup use in syntactic scope and via all semantic paths,
    // recur to syntactic parent until found
    private loc lookupNest(TModel tm, loc scope, Use u){
        if(luDebug)println("\tlookupNest: <scope>, <u>");
        try 
            return lookupQual(tm, scope, u);
        catch NoBinding(): {
            if(tm.scopes[scope] ? && tm.scopes[scope] != scope){
               parent = tm.scopes[scope];
               if(luDebug)println("\tlookupNest: <scope>, <u> move up to <parent>");
               return lookupNest(tm, parent, u);
            }
            if(luDebug) println("\t---- lookupNest, NoBinding: <u>");
            throw NoBinding();
        }
    }
    
    public loc lookup1(TModel tm, Use u){
        scope = u.scope;
        if(luDebug) println("lookup: <u>");
        if(!(u has qualifierRoles)){
           res = lookupNest(tm, scope, u);
           if(isAcceptableSimpleFun(tm, res, u) == acceptBinding()){
              if(luDebug) println("lookup: <u> ==\> <res>");
              return res;
           }
        } else {
           startScope = scope;
           while(true){
              scope = startScope;
               for(id <- u.ids[0..-1]){ 
                   if(luDebug)println("lookup, search for <id>");
                   scope = lookupNest(tm, scope, use(id, u.occ, scope, u.qualifierRoles));
                }
           
                try {
                    res = lookupNest(tm, scope, use(u.ids[-1], u.occ, scope, u.idRoles));
                    if(isAcceptableQualifiedFun(tm, res, u) == acceptBinding()){
                       if(luDebug) println("lookup: <u> ==\> <res>");
                       return res;
                    }
                } catch NoBinding(): {
                      if(tm.scopes[startScope]?){
                         startScope = tm.scopes[startScope];
                         if(luDebug)println("^^^^ lookup move to scope <startScope>");
                      } else {
                         throw NoBinding();
                      }
                }
            }
         }
         if(luDebug) println("---- lookup, NoBinding: <u>");
         throw NoBinding();
    }
    
    public set[loc] lookup(TModel tm, Use u){
        try {
            return {lookup1(tm, u)};
        } catch AmbiguousDefinition(set[loc] definitions):
            return definitions;
    }
    
    /************************************************************************************/
    /* "wide" scopes were designed to suit Rascal's scope model where names from        */
    /* imported modules co-exist with names declared in the current module.             */
    /* lookupWide returns all definitions in the current syntactic scope (or its        */
    /* parents) and definitions that can be reached in a single step via semantic links */                             
    /************************************************************************************/
    
    @memo
    // Retrieve all bindings for use in given syntactic scope
    private set[loc] bindWide(TModel tm, loc scope, str id, set[IdRole] idRoles){
        preDefs = (tm.definesMap[scope] ? ())[id] ? {};
        
        if(isEmpty(preDefs) || isEmpty(preDefs<0> & idRoles)) return {};
        return preDefs<1>;
    }
    
    // Lookup use in the given syntactic scope
    private set[loc] lookupScopeWide(TModel tm, loc scope, Use use){
        //if(wdebug) println("\tlookupScopeWide: <use.id> in scope <scope>");
    
        return {def | def <-  bindWide(tm, scope, use.id, use.idRoles), isAcceptableSimpleFun(tm, def, use) == acceptBinding()}; 
    }
    
    @memo
    // Find all (semantics induced, one-level) bindings for use in given syntactic scope via PathRole
    private set[loc] lookupPathsWide(TModel tm, loc scope, Use use, PathRole pathRole){
        //if(wdebug) println("\tlookupPathsWide: <use.id> in scope <scope>, role <pathRole>\n<for(p <- tm.paths){>\t---- <p>\n<}>");
        res = {};
        
        seenParents = {};
        solve(res, scope) {
        next_path:
            for(<scope, pathRole, loc parent> <- tm.paths, parent notin seenParents){
                seenParents += parent;
                //if(wdebug) println("\tlookupPathsWide: scope: <scope>, trying semantic path to: <parent>");
                
                for(loc def <- lookupScopeWide(tm, parent, use)){
                    switch(isAcceptablePathFun(tm, parent, def, use, pathRole)){
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
    private set[loc] lookupQualWide(TModel tm, loc scope, Use u){
        //if(wdebug) println("\tlookupQualWide: <u.id> in scope <scope>");
      
        res = lookupScopeWide(tm, scope, u);
        //if(wdebug) println("\tlookupQualWide: <u.id> in scope <scope>, after lookupScopeWide:\n<for(r <- res){>\t--\> <r><}>");
       
        //if(wdebug) println("\tlookupQualWide: <res>, loop over <pathRoles(tm)>");
        nextPath:
        for(PathRole pathRole <- pathRoles(tm)){
           candidates = lookupPathsWide(tm, scope, u, pathRole);
           //if(wdebug) println("\tlookupQualWide: candidates: <candidates>");
           for(loc candidate <- candidates){
               switch(isAcceptableSimpleFun(tm, candidate, u)){
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
    private set[loc] lookupNestWide(TModel tm, loc scope, Use u){
        //if(wdebug) println("\tlookupNestWide: <u.id> in scope <scope>");
       
        res = lookupQualWide(tm, scope, u);
        //if(wdebug) println("\tlookupNestWide: <u.id> in scope <scope> found:\n<for(r <- res){>\t==\> <r><}>");
        if(!isEmpty(res)) return res; // <<<
    
        if(tm.scopes[scope] ?){
          if(scope == tm.scopes[scope]) { println("Identical scope in lookupNestWide: <scope>"); return res; }
           parent = tm.scopes[scope];
           //if(wdebug) println("\tlookupNestWide: <u.id> in scope <scope> move up to <parent>");
           res += lookupNestWide(tm, parent, u);
        }
      
        return res;
    }
    
    public set[loc] lookupWide(TModel tm, Use u){
        scope = u.scope;
     
        //if(wdebug) println("lookupWide: <u>");
        if(!(u has qualifierRoles)){
           defs = {def | loc def <- lookupNestWide(tm, scope, u), isAcceptableSimpleFun(tm, def, u) == acceptBinding()};
           //if(wdebug) println("lookupWide: <u> returns:\n<for(d <- defs){>\t==\> <d><}>");
           if(isEmpty(defs)) throw NoBinding(); else return defs;
        } else {
           startScope = scope;
           while(true){
               qscopes = {};
               for(str id <- u.ids[0..-1]){ 
                   //if(wdebug) println("lookup, search for <id>"); 
                   qscopes = lookupNestWide(tm, scope, use(id, u.occ, scope, u.qualifierRoles));
                   if(isEmpty(qscopes)) throw NoBinding();
                }
    
                defs = {};
                for(loc qscope <- qscopes){
                    scopeLookups = lookupNestWide(tm, qscope, use(u.ids[-1], u.occ, qscope, u.idRoles));
                    defs += { def | def <- scopeLookups, isAcceptableQualifiedFun(tm, def, u) == acceptBinding()};            
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
                        qscopes = lookupNestWide(tm, scope, use(id, u.occ, scope, u.qualifierRoles));
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
    
    set[loc] (TModel, Use) lookupFun                               = lookupWide;
    Accept (TModel tm, loc def, Use use) isAcceptableSimpleFun     = tc.isAcceptableSimple;
    Accept (TModel tm, loc def, Use use) isAcceptableQualifiedFun  = tc.isAcceptableQualified;
    Accept (TModel tm, loc defScope, loc def, Use use, PathRole pathRole) isAcceptablePathFun 
                                                                   = tc.isAcceptablePath;
       
    return scopegraph(
            lookupFun
        );
}
 
