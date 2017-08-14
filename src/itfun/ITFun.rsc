module itfun::ITFun
// Functional language with inferred types (MiniML-like)

extend ExtractFRModel;
extend Constraints;
extend TestFramework;

// ----  ITFun syntax ------------------------------------

lexical Id  = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Integer = [0-9]+ !>> [0-9]; 
lexical Boolean = "true" | "false";

keyword Reserved = "true" | "false" | "if" | "then" | "else" | "fi" | "let" | "in" | "fun" | "end";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
   | @category="Comment" ws3: "{" ![\n}]*  "}"$
   ;
 
start syntax Expression 
   = 
     Id name
   | Integer intcon 
   | Boolean boolcon
   | bracket "(" Expression e ")"                   
   > left ( Expression lhs "+" Expression rhs                                          
          | Expression lhs "&&" Expression rhs  
          )
   | "fun" Id name "{" Expression exp "}"
   | Expression exp1 "(" Expression exp2  ")"
   | "let" Id name "=" Expression exp1 "in" Expression exp2 "end"
   | "if" Expression cond "then" Expression thenPart "else" Expression elsePart "fi" 
   ;

// ----  IdRoles, PathLabels and AType ------------------- 

data IdRole
    = variableId()
    ;

data AType   
    = intType()                                     // int type
    | boolType()                                    // bool type
    | functionType(AType from, AType to)            // function type
    ;

str AType2String(intType()) = "int";
str AType2String(boolType()) = "bool";
str AType2String(functionType(AType from, AType to)) = "fun <AType2String(from)> -\> <AType2String(to)>";

// ----  Define ------------------------------------------------------

Tree define(e: (Expression) `fun <Id name> { <Expression body> }`, Tree scope, FRBuilder frb) {   
     sigma1 = frb.newTypeVar(e); 
     sigma2 = frb.newTypeVar(e);
     frb.define(e, "<name>", variableId(), name, defInfo(sigma1));
     frb.fact(e, [], AType() { return functionType(sigma1, sigma2); } );
     frb.fact(body, [], AType(){ return sigma2; } );
     return e;
}

Tree define(e: (Expression) `let <Id name> = <Expression exp1> in <Expression exp2> end`, Tree scope, FRBuilder frb) {  
     frb.define(e, "<name>", variableId(), name, defInfo([exp1], AType() { return typeof(exp1); })); // <<<
     frb.fact(e, [exp2], AType() { return typeof(exp2); });
     return exp2;  
}

// ----  Collect uses & requirements ------------------------------------

void collect(e: (Expression) `<Id name>`, Tree scope, FRBuilder frb){
     frb.use(scope, name, {variableId()});
}

void collect(e: (Expression) `<Expression exp1>(<Expression exp2>)`, Tree scope, FRBuilder frb) { 
     frb.require("application", e, [exp1, exp2],
         () { tau1 = frb.newTypeVar(e); 
              tau2 = frb.newTypeVar(e); 
              if(unify(functionType(tau1, tau2), typeof(exp1))){ 
                 unify(typeof(exp2), tau1, onError(exp2, "Incorrect type of actual parameter"));
                 fact(e, tau2);
              } else { 
                 reportError(exp1, "Function type expected", [exp1]);
              } 
            });
}

void collect(e: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, Tree scope, FRBuilder frb){
     frb.require("if", e, [cond, thenPart, elsePart],
         () { unify(typeof(cond), boolType(), onError(cond, "Condition"));
              unify(typeof(thenPart), typeof(elsePart), onError(e, "thenPart and elsePart should have same type"));
              fact(e, typeof(thenPart)); 
            }); 
}

void collect(e: (Expression) `<Expression lhs> + <Expression rhs>`, Tree scope, FRBuilder frb){
     frb.require("addition", e, [lhs, rhs],
         () { unify(typeof(lhs), intType(), onError(lhs, "Lhs of +"));
              unify(typeof(rhs), intType(), onError(rhs, "Rhs of +"));
              fact(e, intType());
            });
} 

void collect(e: (Expression) `<Expression lhs> && <Expression rhs>`, Tree scope, FRBuilder frb){
     frb.require("and", e, [lhs, rhs],
         () { unify(typeof(lhs), boolType(), onError(lhs, "Lhs of &&"));
              unify(typeof(rhs), boolType(), onError(rhs, "Rhs of &&"));
              fact(e, intType());
            });
}

void collect(e: (Expression) `( <Expression exp> )`, Tree scope, FRBuilder frb){
     frb.fact(e, [exp], AType() { return typeof(exp); });
}

void collect(e: (Expression) `<Boolean boolcon>`, Tree scope, FRBuilder frb){
     frb.atomicFact(e, boolType());
}

void collect(e: (Expression) `<Integer intcon>`, Tree scope, FRBuilder frb){
     frb.atomicFact(e, intType());
}

// ----  Examples & Tests --------------------------------

private Expression sample(str name) = parse(#Expression, |project://TypePal/src/itfun/<name>.it|);

set[Message] validateIT(str name) {
    p = sample(name);
    return validate(extractScopesAndConstraints(p, makeFRBuilder()));
}

void testIT() {
    runTests(|project://TypePal/src/itfun/tests.ttl|, #Expression);
}