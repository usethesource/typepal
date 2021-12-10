module analysis::typepal::ICollector

extend analysis::typepal::ConfigurableScopeGraph;

// The API of TypePal's fact and constraint collector

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
                         void (value l, value r, FailMessage fm) requireUnify
      ); 