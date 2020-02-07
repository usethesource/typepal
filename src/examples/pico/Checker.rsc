module examples::pico::Checker

import examples::pico::Syntax;
 
extend analysis::typepal::TypePal;

// ----  IdRoles, PathLabels and AType ------------------- 

data AType = intType() | strType(); 

str prettyAType(intType()) = "int";
str prettyAType(strType()) = "str";

// ----  Collect definitions, uses and requirements -----------------------

void collect(current: (Program) `begin <Declarations decls> <{Statement  ";"}* body> end`, Collector c){
    c.enterScope(current);
        collect(decls, body, c);
    c.leaveScope(current);
}

void collect(current: (Declarations) `declare <{Declaration ","}* decls> ;`, Collector c){
    collect(decls, c);
}  

void collect(current:(Type) `natural`, Collector c){
    c.fact(current, intType());
}

void collect(current:(Type) `string`, Collector c){
    c.fact(current, strType());
}
 
void collect(current:(Declaration) `<Id id> : <Type tp>`,  Collector c) {
     c.define("<id>", variableId(), id, defType(tp));
     collect(tp, c);
}

void collect(current: (Expression) `<Id name>`, Collector c){
     c.use(name, {variableId()});
}

void collect(current: (Statement) `<Id var> := <Expression val>`, Collector c){
     c.use(var, {variableId()});
     c.requireEqual(var, val, error(current, "Lhs %t should have same type as rhs", var));
     collect(val, c);
}

void collect(current: (Statement) `if <Expression cond> then <{Statement ";"}*  thenPart> else <{Statement ";"}* elsePart> fi`, Collector c){
     c.requireEqual(cond, intType(), error(cond, "Condition should be `int`, found %t", cond));
     collect(cond, thenPart, elsePart, c);
}

void collect(current: (Statement) `while <Expression cond> do <{Statement ";"}* body> od`, Collector c){
     c.requireEqual(cond, intType(), error(cond, "Condition should be `int`, found %t", cond));
     collect(cond, body, c);
}

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, Collector c){
     c.calculate("addition", current, [lhs, rhs], 
        AType (Solver s) { switch([s.getType(lhs), s.getType(rhs)]){
                   case [intType(), intType()]: return intType();
                   case [strType(), strType()]: return strType();
                   default: {
                       s.report(error(current, "Operator `+` cannot be applied to %t and %t", lhs, rhs));
                       return intType();
                     }
                   }
                 });
     collect(lhs, rhs, c);
}

void collect(current: (Expression) `<Expression lhs> - <Expression rhs>`, Collector c){
    c.requireEqual(lhs, intType(), error(lhs, "Left argument of `-` should be `int`, found %t", lhs));
    c.requireEqual(rhs, intType(), error(rhs, "Right argument of `-` should be `int`, found %t", rhs));
    c.fact(current, intType());
    collect(lhs, rhs, c);
}
 
void collect(current: (Expression) `<String string>`, Collector c){
    c.fact(current, strType());
}

void collect(current: (Expression) `<Natural natcon>`, Collector c){
    c.fact(current, intType());
}