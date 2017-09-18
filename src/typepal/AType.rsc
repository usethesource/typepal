module typepal::AType

import String;
extend typepal::ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc name)                            // type variable, used for type inference
    | useType(Use use)                          // Use a type defined elsewhere
    | lazyLub(list[AType] atypes)               // lazily computed LUB of a list of types
    | atypeList(list[AType] atypes)              // built-in list-of-ATypes type
    | overloadedType(rel[Key, AType] overloads) // built-in-overloaded type; each key provides an alternative type
    ;

// Pretty print ATypes
str AType2String(tvar(loc name))    = "<name>";
str AType2String(useType(Use use)) = "<getId(use)>";
str AType2String(lazyLub(list[AType] atypes)) = "lub(<atypes>))";
str AType2String(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [AType2String(a) | a <- atypes]);
str AType2String(overloadedType(rel[Key, AType] overloads)) = "overloaded(" + intercalate(", ", [AType2String(t) | <k, t> <- overloads]) + ")";
default str AType2String(AType tp) = "<tp>";
