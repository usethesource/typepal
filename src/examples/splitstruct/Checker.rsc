module examples::splitstruct::Checker

import examples::splitstruct::Syntax;
 
extend analysis::typepal::TypePal;

// ---- Extend Typepal's ATypes, IdRoles and PathRoles ------------------------

data AType
    = intType()
    | strType()
    | structType(str name)
    ;
    
data IdRole
    = fieldId()
    | structId()
    ;

str prettyAType(intType()) = "int";
str prettyAType(strType()) = "str";
str prettyAType(structType(name)) = "struct <name>";

bool subtype(AType a, a) = true;
bool subtype(AType a, overloadedAType(rel[loc, IdRole, AType] overloads)) = a in overloads<2>;
bool subtype(overloadedAType(rel[loc, IdRole, AType] overloads), AType b) = all(x <- overloads<2>, subtype(x, b));
default bool subtype(AType a, AType b) = false;

tuple[list[str] typeNames, set[IdRole] idRoles] structGetTypeNamesAndRole(structType(str name)){
    return <[name], {structId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] structGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

// Define the name overloading that is allowed: only structIds
bool splitRecordMayOverload(set[loc] defs, map[loc, Define] defines){
    return all(def <- defs, defines[def].idRole == structId());
}

TypePalConfig splitstructConfig() =
    tconfig(
        getTypeNamesAndRole = structGetTypeNamesAndRole,
        mayOverload         = splitRecordMayOverload,
        isSubType           = subtype
    );

// ---- Collect facts and constraints -----------------------------------------

void collect(current:(Declaration)`<Type typ> <Id id> = <Expression exp> ;`, Collector c) {
    c.define(id, variableId(), current, defType(typ));
    c.requireSubType(typ, exp, error(exp, "Incorrect initialization, expected %t, found %t", typ, exp)); /* use subtype instrad of equal */
    collect(typ, exp, c);
}

void collect(current:(Declaration)`struct <Id name> { <{Field ","}* fields> };`, Collector c) {
    c.define(name, structId(), current, defType(structType("<name>"))); 
    c.enterScope(current);
        collect(fields, c);
    c.leaveScope(current);
}

void collect(current:(Field)`<Type typ> <Id name>`, Collector c) {
    c.define(name, fieldId(), current, defType(typ));
    collect(typ, c);
}

void collect(current:(Type)`int`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Type)`str`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(Type)`<Id name>`, Collector c) {
    c.use(current, {structId()});
}

void collect(current:(Expression) `new <Id name>`, Collector c){
    c.use(name, {structId()});
    c.fact(current, structType("<name>"));
}
   
void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, Collector c) {
    c.useViaType(lhs, fieldName, {fieldId()});
    c.fact(current, fieldName);
    collect(lhs, c);
}

void collect(current:(Expression)`<Integer _>`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(Expression)`<Id use>`, Collector c) {
    c.use(use, {variableId()});
}