@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::fun::Checker
 
// Functional language with declared types
 
import examples::fun::Syntax;
 
extend analysis::typepal::TypePal;


// ----  IdRoles, PathLabels and AType ---------------------------------------- 

data AType   
    = boolType()    
    | intType()                                     
    | strType()                            
    | functionType(AType from, AType to)
    ; 

str prettyAType(boolType()) = "bool";
str prettyAType(intType()) = "int";
str prettyAType(strType()) = "str";
str prettyAType(functionType(AType from, AType to)) = "fun <prettyAType(from)> -\> <prettyAType(to)>";

//  Type

void collect(current: (Type) `bool`, Collector c){
    c.fact(current, boolType());
} 

void collect(current: (Type) `int`, Collector c){
    c.fact(current, intType());
} 

void collect(current: (Type) `str`, Collector c){
    c.fact(current, strType());
} 

void collect(current: (Type) `<Type from> -\> <Type to>`, Collector c){
    c.calculate("function type", current, [from, to],
        AType(Solver s){ return functionType(s.getType(from), s.getType(to)); });
    collect(from, to, c);
}

// ----  function declaration

void collect(current: (Expression) `fun <Id name> : <Type tp> { <Expression body> }`, Collector c) {   
     c.enterScope(current);
        c.define("<name>", variableId(), name, defType(tp));
        c.calculate("function declaration", current, [body], AType(Solver s){ return functionType(s.getType(tp), s.getType(body)); });
        collect(tp, body, c);
     c.leaveScope(current);
}

// ---- let

void collect(current: (Expression) `let <Id name> : <Type tp> = <Expression exp1> in <Expression exp2> end`, Collector c) {  
     c.enterScope(current);
         c.define("<name>", variableId(), name, defType(tp));
         c.calculate("let", current, [exp2], AType(Solver s) { return s.getType(exp2); } );
         collect(tp, exp1, exp2, c);  
     c.leaveScope(current);
}

// ---- identifier
 
void collect(current: (Expression) `<Id name>`,  Collector c){
     c.use(name, {variableId()});
}

// ---- function application

void collect(current: (Expression) `<Expression exp1> (<Expression exp2>)`, Collector c) { 
     c.calculate("application", current, [exp1, exp2],
         AType (Solver s) {  
            if(functionType(tau1, tau2) := s.getType(exp1)){
                  s.requireEqual(exp2, tau1, error(exp2, "Incorrect type of actual parameter"));
                  return tau2;
               } else {
                  s.report(error(exp1, "Function type expected"));
                  return intType();
               }
        });
     collect(exp1, exp2, c);
}

// ---- if-then-else

void collect(current: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, Collector c){
     c.calculate("if", current, [cond, thenPart, elsePart],
        AType (Solver s) { 
            s.requireEqual(cond, boolType(), error(cond, "Condition should havwe type `bool`, found %t", cond));
            s.requireEqual(thenPart, elsePart, error(current, "thenPart and elsePart should have same type"));
            return s.getType(thenPart);
        }); 
      collect(cond, thenPart, elsePart, c);
}

// ---- addition/concatenation

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, Collector c){
     c.calculate("addition", current, [lhs, rhs],
        AType (Solver s) { 
            switch(<s.getType(lhs), s.getType(rhs)>){
                case <intType(), intType()>: return intType();
                case <strType(), strType()>: return strType();
                default: {
                    s.report(error(current, "Arguments of type %t and %t not allowed for `+`", lhs, rhs));
                    return intType();
                  }
            }
        });
      collect(lhs, rhs, c);
} 

// ---- and

void collect(current: (Expression) `<Expression lhs> && <Expression rhs>`, Collector c){
     c.calculate("and", current, [lhs, rhs],
        AType (Solver s) { 
            s.requireEqual(lhs, boolType(), error(lhs, "Left argument of `&&` should have type `bool`, found %t", lhs));
            s.requireEqual(rhs, boolType(), error(rhs, "Right argument of `&&` should have type `bool`, found %t", rhs));
            return boolType();
        });
      collect(lhs, rhs, c);
} 

// ---- brackets

void collect(current: (Expression) `( <Expression exp> )`, Collector c){
     c.calculate("bracket", current, [exp], AType(Solver s){ return s.getType(exp); });
     collect(exp, c);
}

// ---- constants

void collect(current: (Expression) `<Boolean boolcon>`, Collector c){
     c.fact(current, boolType());
}

void collect(current: (Expression) `<Integer intcon>`, Collector c){
     c.fact(current, intType());
}

void collect(current: (Expression) `<String strcon>`, Collector c){
     c.fact(current, strType());
}

