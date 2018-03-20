module analysis::typepal::TypePalConfig

import analysis::typepal::AType;
extend analysis::typepal::ScopeGraph;
import analysis::typepal::TypePal;
import util::Reflective;
import String;

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
    println("defaultMayOverload: <defs>");
    return false;
}

str defaultUnescapeName(str s) { return replaceAll(s, "\\", ""); }

// Extends TypePalConfig defined in analysis::typepal::ScopeGraph

data TypePalConfig(
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
        str(str) unescapeName                                       
            = str (str s) { return replaceAll(s, "\\", ""); }
    );