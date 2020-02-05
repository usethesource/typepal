module analysis::typepal::ISolver

extend analysis::typepal::TypePalConfig;
import analysis::typepal::FailMessage;

// The API of TypePal's constraint solver

data Solver
    = solver(
    /* Lifecycle */     TModel () run,
    /* Types */         AType(value) getType,
                        AType (Tree occ, loc scope, set[IdRole] idRoles) getTypeInScope,
                        AType (str name, loc scope, set[IdRole] idRoles) getTypeInScopeFromName,
                        AType (AType containerType, Tree selector, set[IdRole] idRolesSel, loc scope) getTypeInType,
                        rel[str id, AType atype] (AType containerType, loc scope, set[IdRole] idRoles) getAllDefinedInType,
    /* Fact */          void (value, AType) fact,
                        void (value, AType) specializedFact,
    /* Calculate & Require */    
                        bool (value, value) equal,
                        void (value, value, FailMessage) requireEqual,
       
                        bool (value, value) unify,
                        void (value, value, FailMessage) requireUnify,
        
                        bool (value, value) comparable,
                        void (value, value, FailMessage) requireComparable,
                        
                        bool (value, value) subtype,
                        void (value, value, FailMessage) requireSubType,
                        
                        AType (value, value) lub,
                        AType (list[AType]) lubList,
        
                        void (bool, FailMessage) requireTrue,
                        void (bool, FailMessage) requireFalse,
        
    /* Inference */     AType (AType atype) instantiate,
                        bool (AType atype) isFullyInstantiated,
    
    /* Reporting */     bool(FailMessage fm) report,
                        bool (list[FailMessage]) reports,
                        void (list[Message]) addMessages,
                        bool () reportedErrors,
    /* Global Info */   TypePalConfig () getConfig,
                        map[loc, AType]() getFacts,
                        Paths() getPaths,
                        value (str key) getStore,
                        value (str key, value val) putStore,
                        set[Define] (str id, loc scope, set[IdRole] idRoles) getDefinitions,    // deprecated
                        set[Define] () getAllDefines,
                        Define(loc) getDefine
    );