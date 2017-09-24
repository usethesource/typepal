module typepal::AType

import String;
extend typepal::ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc name)                            // type variable, used for type inference
    //| useType(Use use)                          // Use a type defined elsewhere
    | lazyLub(list[AType] atypes)               // lazily computed LUB of a list of types
    | atypeList(list[AType] atypes)              // built-in list-of-ATypes type
    | overloadedAType(rel[Key, AType] overloads) // built-in-overloaded type; each key provides an alternative type
    ;

// Pretty print ATypes
str prettyPrintAType(tvar(loc name))    = "<name>";
//str AType2String(useType(Use use)) = "<getId(use)>";
str prettyPrintAType(lazyLub(list[AType] atypes)) = "lub(<atypes>))";
str prettyPrintAType(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [prettyPrintAType(a) | a <- atypes]);
str prettyPrintAType(overloadedAType(rel[Key, AType] overloads)) = "overloaded(" + intercalate(", ", [prettyPrintAType(t) | <k, t> <- overloads]) + ")";
default str prettyPrintAType(AType tp) = "<tp>";
