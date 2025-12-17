@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::ICollector

/*
    Declaration of the ICollector interface; this is the API of TypePal's fact and constraint collector
*/

extend analysis::typepal::ConfigurableScopeGraph;

data Collector 
    = collector(
      /* Life cycle */   TModel () run,
      
     /* Configuration */ TypePalConfig () getConfig,
                         void (TypePalConfig cfg) setConfig,
                         
     /* Scoping */       void (Tree tree) enterScope,
                         void (list[Tree] trees) enterCompositeScope,
                         void (Tree tree) enterLubScope,
                         void (list[Tree] trees) enterCompositeLubScope,
                         void (Tree tree) leaveScope,
                         void (list[Tree] trees) leaveCompositeScope,
                         loc () getScope,
                         
     /* Scope Info */    void (loc scope, ScopeRole scopeRole, value info) setScopeInfo,
                         lrel[loc scope, value scopeInfo] (ScopeRole scopeRole) getScopeInfo,

     /* Nested Info */   void(str key, value val) push,
                         value (str key) pop,
                         value (str key) top,
                         list[value] (str key) getStack,
                         void (str key) clearStack,

     /* Composition */   void (TModel tm) addTModel,

     /* Reporting */     bool (FailMessage msg) report,
                         bool (list[FailMessage] msgs) reports,

     /* Define */        void (str id, IdRole idRole, value def, DefInfo info) define,
                         void (value scope, str id, IdRole idRole, value def, DefInfo info) defineInScope,
                         Tree (str id, IdRole idRole, value def, DefInfo info) predefine,
                         Tree (value scope, str id, IdRole idRole, DefInfo info) predefineInScope,
                         bool (str id, Tree useOrDef) isAlreadyDefined,

     /* Use */           void (Tree occ, set[IdRole] idRoles) use,
                         void (list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles) useQualified,
                         void (Tree container, Tree selector, set[IdRole] idRolesSel) useViaType,
                         void (Tree occ, set[IdRole] idRoles) useLub,
 
     /* Path */          void (Tree occ, set[IdRole] idRoles, PathRole pathRole) addPathToDef,
                         void (list[str] ids, Tree occ, set[IdRole] idRoles, set[IdRole] qualifierRoles, PathRole pathRole) addPathToQualifiedDef, 
                         void (Tree occ, PathRole pathRole) addPathToType,
                       
     /* Inference */     AType (value src) newTypeVar,

     /* Fact */          void (Tree src, value atype) fact,

     /* GetType */       AType(Tree src) getType,

     /* Calculate */     void (str name, Tree src, list[value] dependencies, AType(Solver s) getAType) calculate,
                         void (str name, Tree src, list[value] dependencies, AType(Solver s) getAType) calculateEager,

     /* Require */       void (str name, Tree src, list[value] dependencies, void(Solver s) preds) require,
                         void (str name, Tree src, list[value] dependencies, void(Solver s) preds) requireEager,
        
                         void (value l, value r, FailMessage fm) requireEqual,
                         void (value l, value r, FailMessage fm) requireComparable,
                         void (value l, value r, FailMessage fm) requireSubType,
                         void (value l, value r, FailMessage fm) requireUnify,

    /* blocked short-hands for scope stack and info stack management (default kwparams) */

    /* enter/leave */   void (Tree id, void () block) scope = (Tree id, void() block) {
                            enterScope(id);
                            try
                                block();
                            catch 22: ;
                            finally
                                leaveScope(id);
                        },
    /* lub ent/leave */ void (Tree id, void () block) lubScope = (Tree id, void() block) {
                            enterLubScope(id);
                            try
                                block();
                            catch 22: ;
                            finally
                                leaveScope(id);
                        },
    /* comp lub */      void (list[Tree] ids, void () block) compositeLubScope = (list[Tree] ids, void () block) {
                            enterCompositeLubScope(ids);
                            try 
                                block();
                            catch 22: ;
                            finally 
                                leaveCompositeScope(ids);
                        },
    /* comp ent/leave*/ void (list[Tree] ids, void () block) compositeScope = (list[Tree] ids, void () block) {
                            enterCompositeScope(ids);
                            try 
                                block();
                            catch 22: ;
                            finally 
                                leaveCompositeScope(ids);
                            
                        },
    /* push/pop info*/  void (str key, value val, void () block) nestInfo = (str key, value val, void () block) {
                            push(key, val);
                            try {
                                block();
                            }
                            catch 22: ;
                            finally {
                                pop(key);
                            }
                        }
      ); 