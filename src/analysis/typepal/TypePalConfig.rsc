module analysis::typepal::TypePalConfig

extend analysis::typepal::Solver;
extend analysis::typepal::AType;
extend analysis::typepal::ScopeGraph;

import String;
extend ParseTree;

syntax ANONYMOUS_OCCURRENCE = "anonymous_occurence";
private loc anonymousOccurrence = ([ANONYMOUS_OCCURRENCE] "anonymous_occurence")@\loc;

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

bool defaultMayOverload (set[loc] defs, map[loc, Define] defines) {
    return false;
}

 AType defaultInstantiateTypeParameters(Tree current, AType def, AType ins, AType act, Solver s){ 
   throw TypePalUsage("`instantiateTypeParameters(<prettyAType(def)>, <prettyAType(ins)>, <prettyAType(act)>)` called but is not specified in TypePalConfig");
}

tuple[list[str] typeNames, set[IdRole] idRoles] defaultGetTypeNamesAndRole(AType atype){
    throw TypePalUsage("`useViaType` used without definition of `getTypeNamesAndRole`");
}

AType defaultGetTypeInNamelessType(AType containerType, Tree selector, loc scope, Solver s){
    throw TypePalUsage("`useViaType` used without definition of `getTypeInNamelessType`");
}

AType defaultGetTypeInTypeFromDefine(Define containerDef, str selectorName, set[IdRole] idRolesSel, Solver s) {
    throw NoBinding();
}   
  
str defaultUnescapeName(str s) { return replaceAll(s, "\\", ""); }

bool defaultReportUnused (loc def, map[loc,Define] definitions, map[loc,loc] scopes, TypePalConfig config) {
    return false;
}

// Extends TypePalConfig defined in analysis::typepal::ScopeGraph

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
            = bool (set[loc] defs, map[loc, Define] defines) { return false; },
            
        bool (IdRole idRole) isInferrable
            = bool(IdRole idRole) { return false; },
        
        str(str) unescapeName                                       
            = str (str s) { return replaceAll(s, "\\", ""); },
        
        AType (Tree selector, AType def, AType ins, AType act, Solver s) instantiateTypeParameters 
            = AType(Tree selector, AType def, AType ins, AType act, Solver s){ return act; },
       
        tuple[list[str] typeNames, set[IdRole] idRoles] (AType atype) getTypeNamesAndRole
            = tuple[list[str] typeNames, set[IdRole] idRoles](AType atype){
                throw TypePalUsage("`useViaType` used without definition of `getTypeNamesAndRole`");
            },
            
        AType (Define containerDef, str selectorName, set[IdRole] idRolesSel, Solver s) getTypeInTypeFromDefine
            = AType (Define containerDef, str selectorName, set[IdRole] idRolesSel, Solver s) { throw NoBinding(); },
 
        AType(AType containerType, Tree selector, loc scope, Solver s) getTypeInNamelessType
            = AType(AType containerType, Tree selector, loc scope, Solver s){
                throw TypePalUsage("`useViaType` used without definition of `getTypeInNamelessType`");
            }, 
            
        TModel(map[str,Tree] namedTrees, TModel tm) preSolver = TModel(map[str,Tree] namedTrees, TModel tm) { return tm; },    
        void (map[str,Tree] namedTrees, Solver s) postSolver  = void(map[str,Tree] namedTrees, Solver s) { return ; },
        
        bool(loc def, map[loc,Define] definitions, map[loc,loc] scopes, TypePalConfig config) reportUnused = defaultReportUnused
    );