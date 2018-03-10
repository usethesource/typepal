module analysis::typepal::TypePalConfig

import analysis::typepal::AType;
import analysis::typepal::ScopeGraph;
import analysis::typepal::TypePal;
import util::Reflective;

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

bool defaultMayOverload (set[Key] defs, map[Key, Define] defines) {
    return false;
}

AType defaultExpandPreAType(AType atype, loc scope) {
    return atype;
}

// Extends TypePalConfig defined in analysis::typepal::ScopeGraph

data TypePalConfig(
        AType() getMinAType                                         = defaultGetMinAType,
        AType() getMaxAType                                         = defaultGetMaxAType,
        bool (AType t1, AType t2) isSubType                         = defaultIsSubType,
        AType (AType t1, AType t2) getLub                           = defaultGetLub,        
        bool (set[Key] defs, map[Key, Define] defines) mayOverload  = defaultMayOverload
        //AType (AType, Key) expandPreAType                           = defaultExpandPreAType
    );