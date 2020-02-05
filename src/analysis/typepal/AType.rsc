module analysis::typepal::AType
  
import List;
extend analysis::typepal::TModel;

// Foundation of ATypes, will be extended for different type systems

data AType
    = tvar(loc tname)                                      // type variable, used for type inference
    | lazyLub(list[AType] atypes)                          // lazily computed LUB of a list of types
    | atypeList(list[AType] atypes)                        // built-in list-of-ATypes type
    | overloadedAType(rel[loc, IdRole, AType] overloads)   // built-in-overloaded type; each loc provides an alternative type
    ;

// Is an AType overloaded?

bool isOverloadedAType(overloadedAType(rel[loc, IdRole, AType] overloads)) = true;
default bool isOverloadedAType(AType _) = false;

AType lazyLub([*AType atypes1, lazyLub([*AType atypes2]), *AType atypes3]) = lazyLub([*atypes1, *atypes2, *atypes3]);
AType lazyLub([*AType atypes1, AType atypea, *AType atypes2, AType atypeb, *AType atypes3]) = lazyLub([*atypes1, atypea, *atypes2, *atypes3]);
AType lazyLub([AType atype]) = atype;

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

// Pretty print ATypes as string. To be extended forATYpe extensions

str prettyAType(tvar(loc tname))               = "typevar(<tname>)";
str prettyAType(lazyLub(list[AType] atypes))   = "lub(<atypes>))";
str prettyAType(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [prettyAType(a) | a <- atypes]);
default str prettyAType(overloadedAType(rel[loc, IdRole, AType] overloads)) 
                                              = "overloaded: {" + intercalate(", ", [prettyAType(t) | <k, r, t> <- overloads]) + "}";
default str prettyAType(AType tp)              = "<tp>";
       
