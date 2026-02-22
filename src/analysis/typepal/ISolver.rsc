@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::ISolver

/*
    Declaration of the ISolver interface; this is the API of TypePal's constraint solver
*/

extend analysis::typepal::AType;
extend analysis::typepal::FailMessage;
import ParseTree;

data Solver
    = solver(
    /* Lifecycle */     TModel () run,
    /* Types */         AType(value) getType,
                        AType (Tree occ, loc scope, set[IdRole] idRoles) getTypeInScope,
                        AType (str name, loc scope, set[IdRole] idRoles) getTypeInScopeFromName,
                        AType (Tree container, Tree selector, set[IdRole] idRolesSel, loc scope) getTypeInType,
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
                        map[PathRole,rel[loc,loc]]() getPathsByPathRole,
                        set[Define] (str id, loc scope, set[IdRole] idRoles) getDefinitions,    // deprecated
                        set[Define] () getAllDefines,
                        Define(loc) getDefine,
                        rel[loc,loc] () getUseDef,
                        bool(loc,loc) isContainedIn,
                        bool(loc,loc) isBefore,
                        
    /* Nested Info */   void(str key, value val) push,
                        value (str key) pop,
                        value (str key) top,
                        list[value] (str key) getStack,
                        void (str key) clearStack
    )
    | dummySolver()
    ;