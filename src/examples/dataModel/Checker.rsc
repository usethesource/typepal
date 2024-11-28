@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::dataModel::Checker

import examples::dataModel::Syntax;
extend analysis::typepal::TypePal;

// Type basics

data AType 
    = intType() 
    | strType()
    | setType(AType elm)
    | entityType(str name)
    | fieldType(str name)
    ;
    
str prettyAType(intType()) = "int";
str prettyAType(strType()) = "str";
str prettyAType(setType(AType tp)) = "Set\<<prettyAType(tp)>\>";
str prettyAType(entityType(str name)) = name;
str prettyAType(fieldType(str name)) = name;

str prettyAType(functionType(AType from, AType to)) = "fun <prettyAType(from)> -\> <prettyAType(to)>";

data IdRole
    = entityId()
    | fieldId()
    ;
 
tuple[list[str] typeNames, set[IdRole] idRoles] dmGetTypeNamesAndRole(entityType(str name)){
    return <[name], {entityId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] dmGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

TypePalConfig dmConfig() =
    tconfig(getTypeNamesAndRole = dmGetTypeNamesAndRole);

// Collect functions

void collect(current: (Program) `<Declaration+ decls>`, Collector c){
    collect(decls, c);
}

void collect(current: (Declaration) `entity <Id name>  { <Field+ fields> }`, Collector c){
    c.define("<name>", entityId(), current, defType(entityType("<name>")));
    c.enterScope(current);
        collect(fields, c);
    c.leaveScope(current);
}

void collect(current: (Field) `<Id name> -\> <Type typ> inverse <Id ref> :: <Id attr>`, Collector c){
    c.define("<name>", fieldId(), current, defType(typ));
    c.use(ref, {entityId()});
    c.useViaType(ref, attr, {fieldId()});
    c.require("check inverse", current, [attr],
        void(Solver s){
            field_type = s.getType(typ);
            attr_type = s.getType(attr);
            ref_type = s.getType(ref);
            
            if(setType(elm_type) := field_type){
                s.requireEqual(elm_type, ref_type, error(attr, "Field type %t does not match reference type %t", typ, ref)); 
            } else {
                s.requireEqual(ref_type, field_type, error(attr, "Field type %t should be equal to reference type %t", field_type, ref_type));
            }
        });
    collect(typ, ref, attr, c);
}

void collect(current: (Type) `int`, Collector c){
    c.fact(current, intType());
}

void collect(current: (Type) `str`, Collector c){
    c.fact(current, strType());
}

void collect(current: (Type) `<Id tp>`, Collector c){
    c.use(tp, {entityId(), fieldId()});
}

void collect(current: (Type) `Set \< <Type tp> \>`, Collector c){
    c.calculate("set type", current, [tp], AType (Solver s) { return setType(s.getType(tp)); });
    collect(tp, c);
}