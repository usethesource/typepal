module analysis::typepal::TypePalConfig

import analysis::typepal::AType;
import analysis::typepal::ScopeGraph;
import analysis::typepal::TypePal;
import util::Reflective;

AType defaultgetMinAType(){
    throw TypePalUsage("`getMinAType()` called but is not specified in TypePalConfig");
}

AType defaultgetMaxAType(){
    throw TypePalUsage("`getMaxAType()` called but is not specified in TypePalConfig");
}

AType defaultGetLub(AType atype1, AType atype2){
    throw TypePalUsage("`lub(<atype1>, <atype2>)` called but `getLub` is not specified in TypePalConfig");
}

bool defaultIsSubType(AType atype1, AType atype2) {
    throw TypePalUsage("`subtype(<atype1>, <atype2>)` called but `isSubType` is not specified in TypePalConfig");
}

data TypePalConfig(
        PathConfig pathConfig                                       = pathConfig(),
        AType() getMinAType                                         = defaultGetMinAType,
        AType() getMaxAType                                         = defaultGetMaxAType,
        bool (AType t1, AType t2) isSubType                         = defaultIsSubType,
        AType (AType t1, AType t2) getLub                           = defaultGetLub,        
        bool (set[Key] defs, map[Key, Define] defines) mayOverload  = defaultMayOverload
    );