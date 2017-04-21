module TypedMiniML

import Prelude; 
extend Constraints;

lexical Id  = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Integer = [0-9]+ !>> [0-9]; 
lexical Boolean = "true" | "false";

keyword Reserved = "true" | "false" | "if" | "then" | "else" | "fi" | "let" | "in";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "%" ![%]+ "%"
   | @category="Comment" ws3: "%%" ![\n]* $
   ;

syntax Type 
   = "int" 
   | "bool"
   ; 
   
start syntax Expression 
   = 
     @use{variable}
     Id name
   | @fact{int} 
     Integer intcon 
   | @fact{bool} 
     Boolean boolcon
   | @fact{bracket}
     bracket "(" Expression e ")"                   
   > left ( @req{addition}    
            Expression lhs "+" Expression rhs                                          
          | @req{and} 
            Expression lhs "&&" Expression rhs  
          )
   | @def{abstraction} 
     "\\" Id name ":" Type tp "." Expression exp
   | @req{application}
     "(" Expression exp1 Expression exp2  ")"
   | @def{let}
     "let" Id name ":" Type tp "=" Expression exp1 "in" Expression exp2
   | @req{if} 
     "if" Expression cond "then" Expression thenPart "else" Expression elsePart "fi" 
   ;

// Example

public Expression exp1() = parse(#Expression, |project://Scopes/src/examples/e1.tmm|);

public Expression exp2() = parse(#Expression, |project://Scopes/src/examples/e2.tmm|);

// Declare Id roles
data IdRole
    = variableId()
    ;

// Extend Abstract type

data AType   
    = intType()                                     // int type
    | boolType()                                    // bool type
    | functionType(AType from, AType to)            // function type
    ; 

AType transType((Type) `int`) = intType();
AType transType((Type) `bool`) = boolType(); 

str AType2String(intType()) = "`int`";
str AType2String(boolType()) = "`bool`";
str AType2String(functionType(AType from, AType to)) = "`fun <AType2String(from)> -\> <AType2String(to)>`";


Tree define("abstraction", e: (Expression) `\\ <Id name> : <Type tp> . <Expression body>`, Tree scope, SGBuilder sgb) {   
    sgb.define(e, "<name>", variableId(), name, defInfo(transType(tp)));
    sgb.fact(e, functionType(transType(tp), typeof(body)));
    return e;
}

void require("application", e: (Expression) `(<Expression exp1> <Expression exp2>)`, SGBuilder sgb) { 
    sgb.require("application", e, 
                [ match(functionType(tau(1), tau(2)), typeof(exp1), onError(exp1, "Function type expected")), 
                  equal(tau(1), typeof(exp2), onError(exp2, "Incorrect type of actual parameter")),
                  fact(e, tau(1)) 
                ]);
}

Tree define("let", e: (Expression) `let <Id name> : <Type tp> = <Expression exp1> in <Expression exp2>`, Key Tree, SGBuilder sgb) {  
    sgb.define(e, "<name>", variableId(), name, defInfo(transType(tp)));
    sgb.fact(e, typeof(exp2));
    return e;  
}
        
void use("variable", e: (Expression) `<Id name>`, Tree scope, SGBuilder sgb){
    sgb.use(scope, "<name>", name, {variableId()}, 0);
}

void require("if", e: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, SGBuilder sgb){
    sgb.require("if", e, 
                [ equal(typeof(cond), boolType(), onError(cond, "Condition")),
                  equal(typeof(thenPart), typeof(elsePart), onError(e, "thenPart and elsePart should have same type")),
                  fact(e, typeof(thenPart)) 
                ]); 
}

void require("addition", e: (Expression) `<Expression lhs> + <Expression rhs>`, SGBuilder sgb){
     sgb.require("addition", e, 
                 [ equal(typeof(lhs), intType(), onError(lhs, "Lhs of +")),
                   equal(typeof(rhs), intType(), onError(rhs, "Rhs of +")),
                   fact(e, intType()) 
                 ]);
} 

void require("and", e: (Expression) `<Expression lhs> && <Expression rhs>`, SGBuilder sgb){
     sgb.require("and", e, 
                 [ equal(typeof(lhs), boolType(), onError(lhs, "Lhs of &&")),
                   equal(typeof(rhs), boolType(), onError(rhs, "Rhs of &&")),
                   fact(e, intType()) 
                 ]);
} 

void fact("bracket", e :(Expression) `( <Expression exp> )`, SGBuilder sgb){
     sgb.fact(e, typeof(exp));
}

void fact(str kind, Expression e, SGBuilder sgb){
     sgb.fact(e, kind == "int" ? intType() : boolType());
}

void typecheck(Expression e) = validate(extractScopesAndConstraints(e)); 

void validateTMM() = validate(extractScopesAndConstraints(exp1())); 