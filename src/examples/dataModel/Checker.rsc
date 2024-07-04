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
    c.define(name, entityId(), current, defType(entityType("<name>")));
    c.enterScope(current);
        collect(fields, c);
    c.leaveScope(current);
}

void collect(current: (Field) `<Id name> -\> <Type typ> inverse <Id ref> :: <Id attr>`, Collector c){
    c.define(name, fieldId(), current, defType(typ));
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