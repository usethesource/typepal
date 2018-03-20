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
    ;

// Pretty print ATypes
str prettyPrintAType(tvar(loc tname))               = "typevar(<tname>)";
str prettyPrintAType(lazyLub(list[AType] atypes))   = "lub(<atypes>))";
str prettyPrintAType(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [prettyPrintAType(a) | a <- atypes]);
default str prettyPrintAType(overloadedAType(rel[loc, IdRole, AType] overloads)) 
                                                    = "overloaded: {" + intercalate(", ", [prettyPrintAType(t) | <k, r, t> <- overloads]) + "}";
default str prettyPrintAType(AType tp)              = "<tp>";
 
data FailMessage
    = error(value src, str msg)
    | error(value src, str msg, value arg0)
    | error(value src, str msg, value arg0, value arg1)
    | error(value src, str msg, value arg0, value arg1, value arg2)
     | error(value src, str msg, value arg0, value arg1, value arg2, value arg3)
    | warning(value src, str msg)
    | warning(value src, str msg, value arg0)
    | warning(value src, str msg, value arg0, value arg1)
    | warning(value src, str msg, value arg0, value arg1, value arg2)
    | warning(value src, str msg, value arg0, value arg1, value arg2, value arg3)
    | info(value src, str msg)
    | info(value src, str msg, value arg0)
    | info(value src, str msg, value arg0, value arg1)
    | info(value src, str msg, value arg0, value arg1, value arg2)
    | info(value src, str msg, value arg0, value arg1, value arg2, value arg3)
    ;
       
// --- Exceptions

data RuntimeException
    = TypePalUsage(str reason)              // TypePal used incorrectly
    | TypePalInternalError(str reason)      // TypePal internal error
    | TypeUnavailable()                     // Type is not available: used in control flow of solver
    | checkFailed(set[Message] msgs)        // Type check failed: used in control flow of solver
    ;