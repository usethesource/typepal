module examples::smallOO::Checker

import examples::smallOO::Syntax;
 
extend analysis::typepal::TypePal;

// ---- Extend Typepal's ATypes, IdRoles and PathRoles -----------------------
 
data AType
    = intType()
    | strType()
    | classType(str name)
    | functionType(AType returnType, AType formals)
    ;
    
data IdRole
    = fieldId()
    | parameterId()
    | methodId()
    | classId()
    ;

str prettyAType(intType()) = "int";
str prettyAType(strType()) = "str";
str prettyAType(classType(str name)) = name;


tuple[list[str] typeNames, set[IdRole] idRoles] smallGetTypeNamesAndRole(classType(str name)){
    return <[name], {classId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] smallGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

TypePalConfig smallConfig() =
    tconfig(getTypeNamesAndRole = smallGetTypeNamesAndRole);

// ---- collect ---------------------------------------------------------------

void collect(current:(Module)`module <Identifier _> <Import* _> <Declaration* decls>`, Collector c) {
    collect(decls, c);
}

void collect(current:(Declaration)`class <Identifier className> { <Declaration* decls> }`, Collector c) {
    c.define("<className>", classId(), current, defType(classType("<className>")));
    c.enterScope(current);
        collect(decls, c);
    c.leaveScope(current);
}

void collect(current:(Declaration)`<Type returnType> <Identifier functionName> ( <{Parameter ","}* params> ) = <Expression returnExpression> ;`, Collector c) {
    classScope = c.getScope(); 
    c.enterScope(current); {
        c.defineInScope(classScope, "<functionName>", methodId(), functionName, 
            defType(returnType + [p.name | p <- params], AType(Solver s) { return functionType(s.getType(returnType), atypeList([s.getType(p.name) | p <- params])); }));
     
        c.require("return expression", returnExpression, [returnType, returnExpression],
            void (Solver s) {
                s.requireEqual(returnType, returnExpression, error(returnExpression, "Return expression is not the same type as the return type (%t) instead of (%t)", returnExpression, returnType));
        });
        collect(returnType, params, returnExpression, c);
    }
    c.leaveScope(current);
}

void collect(current:(Declaration)`<Type fieldType> <Identifier fieldName>;`, Collector c) {
    c.define("<fieldName>", fieldId(), fieldName, defType(fieldType));
    c.fact(current, fieldType);
    collect(fieldType, c);
}

void collect(current:(Parameter)`<Type paramType> <Identifier paramName>`, Collector c) {
    c.define("<paramName>", parameterId(), paramName, defType(paramType));
    c.fact(current, paramType);
    collect(paramType, c);
}

void collect(current:(Expression)`<Identifier id>`, Collector c) {
    c.use(id, {fieldId(), parameterId(), methodId()});
}

void collect(current:(Type) `int`, Collector c){
    c.fact(current, intType());
}

void collect(current:(Type) `str`, Collector c){
    c.fact(current, strType());
}

void collect(current:(Type) `<Identifier className>`, Collector c){
   c.use(className, {classId()});
}

void collect(current:(Expression)`<Integer _>`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Expression)`<String _>`, Collector c) {
    c.fact(current, strType());
}

void collect(current:(Expression)`<Identifier functionName> ( <{Expression ","}* params> )`, Collector c) {
    c.calculate("call function `<functionName>`", functionName, [functionName] + [ e | e <- params], 
        AType(Solver s) {
            funType = s.getType(functionName);
            parType = atypeList([s.getType(e) | e <- params]);
            return computeCallType(functionName, funType, parType, s);
        });
    collect(params, c);
}

void collect(current:(Expression)`<Expression lhs> . <Identifier id>`, Collector c) {
    c.useViaType(lhs, id, {fieldId()});
    c.fact(current, id);
    collect(lhs, c);           
}

void collect(current:(Expression)`<Expression lhs> . <Identifier functionName> ( <{Expression ","}* params> )`, Collector c) {
    c.useViaType(lhs, functionName, {methodId()});
    c.calculate("method `<functionName>`", current, [p | p <- params],
       AType(Solver s) { 
            funType = s.getType(functionName);
            parType = atypeList([s.getType(e) | e <- params]);
            return computeCallType(functionName, funType, parType, s);
         }); 
    collect(lhs, params, c);  
}

AType computeCallType(Identifier functionName, AType funType, AType parTypes, Solver s){
    switch (funType) {
        case overloadedAType({*_,<_,_, functionType(AType ret, parTypes)>}) : return ret;
        case functionType(AType ret, parTypes): return ret;
        default: s.report(error(functionName, "No function can be found that accepts these parameters: %t", parTypes));
    }
    return intType();
}

void collect(current:(Expression)`<Expression lhs> + <Expression rhs>`, Collector c) {
    c.calculate("expression",current, [lhs, rhs],
        AType(Solver s) {
            switch([s.getType(lhs), s.getType(rhs)]){
                case [intType(), intType()]: return intType();
                case[strType(), strType()]: return strType();
                default: {
                     s.report(error(current, "+ is not defined on %t and %t", lhs, rhs));
                     return intType();
                  }
            }
    });
    collect(lhs, rhs, c);
}
