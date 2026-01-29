@license{
Copyright (c) 2022, Paul Klint, UseTheSource
All rights reserved. 
  
Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met: 
  
1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer. 
  
2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution. 
  
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::AType

/*
    Foundation of ATypes, to be extended for different type systems
*/
  
import List;

extend analysis::typepal::GetLoc;
import analysis::typepal::TModel;

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
    rel[loc, IdRole, AType] flatOverloads = {};
    for(ovl:<_, _, tp> <- overloads){
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
    = any(<_, _, tp> <- overloads, tp is overloadedAType);

// Flatten nested overloads
AType overloadedAType(rel[loc, IdRole, AType] overloads) 
    = overloadedAType(flatten(overloads)) when containsNestedOverloading(overloads); 

// Pretty print ATypes as string. To be extended forATYpe extensions

str prettyAType(tvar(loc tname))               = "typevar(<tname>)";
str prettyAType(lazyLub(list[AType] atypes))   = "lub(<atypes>))";
str prettyAType(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [prettyAType(a) | a <- atypes]);
default str prettyAType(overloadedAType(rel[loc, IdRole, AType] overloads)) 
                                              = "overloaded: {" + intercalate(", ", [prettyAType(t) | <_,_, t> <- overloads]) + "}";
default str prettyAType(AType tp)              = "<tp>";
       
str itemizeLocs(set[loc] locs)
            = "<for(d <- locs){>
              '- <d><}>";