module analysis::typepal::AType

import String;
import List;
import Set;
import Message;
extend analysis::typepal::ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc tname)                                      // type variable, used for type inference
    | lazyLub(list[AType] atypes)                          // lazily computed LUB of a list of types
    | atypeList(list[AType] atypes)                        // built-in list-of-ATypes type
    | overloadedAType(rel[loc, IdRole, AType] overloads)   // built-in-overloaded type; each loc provides an alternative type
    | preAType(str name, AType atype)                     // a "premature" type that will be expanded into a real type when possible
    ;

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
    | checkFailed(set[Message] msgs)        // Type check failed: used in control flow of solver
    ;