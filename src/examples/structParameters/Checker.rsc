module examples::structParameters::Checker

import examples::structParameters::Syntax;
 
extend analysis::typepal::TypePal;

import List;

// ---- Extend Typepal's ATypes, IdRoles and PathRoles ------------------------

data AType
    = intType()
    | strType()
    | typeFormal(str name)
    | structDef(str name, list[str] formals)
    | structType(str name, list[AType] actuals)
    ;
    
data IdRole
    = fieldId()
    | structId()
    | typeFormalId()
    ;

str prettyAType(intType()) = "int";
str prettyAType(strType()) = "str";
str prettyAType(typeFormal(name)) = "<name>";
str prettyAType(structDef(name, formals)) = isEmpty(formals) ? "<name>" : "<name>[<intercalate(",", formals)>]";
str prettyAType(structType(name, actuals)) = isEmpty(actuals) ? "<name>" : "<name>[<intercalate(",", [prettyAType(a) | a <- actuals])>]";

AType structParametersInstantiateTypeParameters(Tree current, structDef(str name1, list[str] formals), structType(str name2, list[AType] actuals), AType t, Solver s){
    if(size(formals) != size(actuals)) throw checkFailed([]);
    bindings = (formals[i] : actuals [i] | int i <- index(formals));
    
    return visit(t) { case typeFormal(str x) => bindings[x] };
}

default AType structParametersInstantiateTypeParameters(Tree current, AType def, AType ins, AType act, Solver s) {
    return act;
}

tuple[list[str] typeNames, set[IdRole] idRoles] structParametersGetTypeNamesAndRole(structType(str name, list[AType] actuals)){
    return <[name], {structId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] structParametersGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

AType structParametersGetTypeInNamelessType(AType containerType, Tree selector, loc scope, Solver s){
    s.report(error(selector, "Undefined field %q on %t", "<selector>", containerType));
}

TypePalConfig structParametersConfig() =
    tconfig(getTypeNamesAndRole = structParametersGetTypeNamesAndRole,
            getTypeInNamelessType = structParametersGetTypeInNamelessType,
            instantiateTypeParameters = structParametersInstantiateTypeParameters);

// ---- Collect facts and constraints -----------------------------------------

void collect(current:(Declaration)`<Type typ> <Id id> = <Expression exp> ;`, Collector c) {
    c.define("<id>", variableId(), current, defType(typ));
    c.requireEqual(typ, exp, error(exp, "Incorrect initialization, expected %t, found %t", typ, exp));
    
    c.enterScope(current);
        collect(typ, exp, c);
    c.leaveScope(current);
}

void collect(current:(Declaration) `struct <Id name> <TypeFormals formals> { <{Field ","}* fields> };`, Collector c) {
    type_formal_list = formals is noTypeFormals ? [] : [f | f <- formals.formals];
    c.define("<name>", structId(), current,  defType(structDef("<name>", [ "<tf>" | tf <- type_formal_list])));
    c.enterScope(current);
        for(tf <- type_formal_list){
            c.define("<tf>", typeFormalId(), tf, defType(typeFormal("<tf>")));
        }
        collect(formals, fields, c);
    c.leaveScope(current);
}

void collect(current:(Field)`<Type typ> <Id name>`, Collector c) {
    c.define("<name>", fieldId(), current, defType(typ));
    collect(typ, c);
} 

// ---- Types -----------------------------------------------------------------

void collect(current:(Type)`int`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Type)`str`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(TypeFormals) `[ <{TypeFormal ","}+ formals> ]`, Collector c){
    collect(formals, c);
}

void collect(current:(TypeActuals) `[ <{Type ","}+ actuals> ]`, Collector c){
    collect(actuals, c);
}

void collect(current: (Type) `<Id name> <TypeActuals actuals>`, Collector c){
    c.use(name, {structId(), typeFormalId()});
    if(actuals is withTypeActuals){
        tpActuals = [tp | tp <- actuals.actuals];
        c.calculate("actual type", current, name + tpActuals,
            AType(Solver s) { 
                return structType("<name>", [s.getType(tp) | tp <- tpActuals]);});
            
        collect(actuals, c);
    } else {
        c.fact(current, name);
    }
}

void collect(current:(Expression) `new <Id name><TypeActuals actuals>`, Collector c){
    c.use(name, {structId()});
    actual_list = actuals is noActuals ? [] : [a | a <- actuals.actuals];
    c.calculate("new `<name>`", current, name + actual_list,
        AType(Solver s){
            if(structDef(nm, formals) := s.getType(name)){
                formal_list = [f | f <- formals];
                if(size(actual_list) != size(formal_list)){
                    s.report(error(actuals, "Expected %v type parameters, but got %v", size(formal_list), size(actual_list)));
                }
            } else {
                s.report(error(name, "Illegal type in `new`, expected `struct` found %t", name));
            }
            return structType("<name>", [s.getType(a) | a <- actual_list]);
        });
    collect(actuals, c);
}
   
void collect(current:(Expression)`<Expression lhs> . <Id fieldName>`, Collector c) {
    c.useViaType(lhs, fieldName, {fieldId()});
    c.calculate("FIELD SELECT", current, [lhs, fieldName],          // Hackish solution, error in Solver?
        AType(Solver s) { 
            tp = s.getType(fieldName); 
            if(typeFormal(str name) := tp) throw TypeUnavailable();
            return tp;
            
            });
    //c.fact(current, fieldName);                                   // <-- this should be enough
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