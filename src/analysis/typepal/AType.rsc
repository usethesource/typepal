module analysis::typepal::AType

import String;
import List;
import Set;
import analysis::typepal::FailMessage;
extend analysis::typepal::ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc tname)                                      // type variable, used for type inference
    | lazyLub(list[AType] atypes)                          // lazily computed LUB of a list of types
    | atypeList(list[AType] atypes)                        // built-in list-of-ATypes type
    | overloadedAType(rel[loc, IdRole, AType] overloads)   // built-in-overloaded type; each loc provides an alternative type
    ;


AType lazyLub([*AType atypes1, lazyLub([*AType atypes2]), *AType atypes3]) = lazyLub([*atypes1, *atypes2, *atypes3]);
AType lazyLub([*AType atypes1, AType atypea, *AType atypes2, AType atypeb, *AType atypes3]) = lazyLub([*atypes1, atypea, *atypes2, *atypes3]);


rel[loc, IdRole, AType] flatten(rel[loc, IdRole, AType] overloads){
    flatOverloads = {};
    for(ovl:<key, idr, tp> <- overloads){
        if(overloadedAType(rel[loc, IdRole, AType] overloads1) := tp){
            flat = false;
            for(ovl1 <- overloads1) flatOverloads += ovl1;
        } else {
            flatOverloads += ovl;
        }
    }
    return flatOverloads;
}

bool containsNestedOverloading(rel[loc, IdRole, AType] overloads)
    = any(<key, idr, tp> <- overloads, tp is overloadedAType);

// Flatten nested overloads
AType overloadedAType(rel[loc, IdRole, AType] overloads) 
    = overloadedAType(flatten(overloads)) when containsNestedOverloading(overloads); 

// Pretty print ATypes
str prettyPrintAType(tvar(loc tname))               = "typevar(<tname>)";
str prettyPrintAType(lazyLub(list[AType] atypes))   = "lub(<atypes>))";
str prettyPrintAType(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [prettyPrintAType(a) | a <- atypes]);
default str prettyPrintAType(overloadedAType(rel[loc, IdRole, AType] overloads)) 
                                                    = "overloaded: {" + intercalate(", ", [prettyPrintAType(t) | <k, r, t> <- overloads]) + "}";
default str prettyPrintAType(AType tp)              = "<tp>";
       
// --- Exceptions

data RuntimeException
    = TypePalUsage(str reason)              // TypePal used incorrectly
    | TypePalInternalError(str reason)      // TypePal internal error
    | TypeUnavailable()                     // Type is not available: used in control flow of solver
    | checkFailed(list[FailMessage] msgs)   // Type check failed: used in control flow of solver
    ;