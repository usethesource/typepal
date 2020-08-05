@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::untypedFun::Checker

// Untyped functional language with inferred types (MiniML-like)

import examples::untypedFun::Syntax;

extend analysis::typepal::TypePal;

// ----  IdRoles, PathLabels and AType ------------------- 

data AType   
    = intType()                                     // int type
    | boolType()                                    // bool type
    | strType()                                     // string type
    | functionType(AType from, AType to)            // function type
    ;

str prettyAType(intType()) = "int";
str prettyAType(boolType()) = "bool";
str prettyAType(strType()) = "str";
str prettyAType(functionType(AType from, AType to)) = "fun <prettyAType(from)> -\> <prettyAType(to)>";

// ----  Collect defines, uses & constraints --------------------------

void collect(current: (Expression) `fun <Id arg> { <Expression body> }`, Collector c) {
    c.enterScope(current);  
        tau1 = c.newTypeVar(arg); 
        tau2 = c.newTypeVar(body);
        c.fact(current, functionType(tau1, tau2));
        c.define("<arg>", variableId(), arg, defType(tau1));
        collect(body, c);
     c.leaveScope(current);
}

void collect(current: (Expression) `<Expression exp1>(<Expression exp2>)`, Collector c) { 
     tau1 = c.newTypeVar(exp1); 
     tau2 = c.newTypeVar(exp2); 
  
     c.calculateEager("application", current, [exp1, exp2],
        AType (Solver s) { 
              s.requireUnify(functionType(tau1, tau2), exp1, error(exp1, "Function type expected, found %t", exp1));
              s.requireUnify(tau1, exp2, error(exp2, "Incorrect type of actual parameter"));             
              return tau2;
            });
      collect(exp1, exp2, c);
}


void collect(current: (Expression) `let <Id name> = <Expression exp1> in <Expression exp2> end`, Collector c) { 
    c.enterScope(current); 
        c.define("<name>", variableId(), name, defType(exp1));
        c.fact(current, exp2);
        collect(exp1, exp2, c);
    c.leaveScope(current);
}

void collect(current: (Expression) `if <Expression cond> then <Expression thenPart> else <Expression elsePart> fi`, Collector c){
     c.calculate("if", current, [cond, thenPart, elsePart],
        AType (Solver s) { 
            s.requireUnify(cond, boolType(), error(cond, "Condition"));
            s.requireUnify(thenPart, elsePart, error(current, "thenPart and elsePart should have same type"));
            return s.getType(thenPart); 
        }); 
     collect(cond, thenPart, elsePart, c);
}

void collect(current: (Expression) `<Expression lhs> + <Expression rhs>`, Collector c){
     c.calculateEager("addition", current, [lhs,rhs],
         AType (Solver s) { 
            targs = atypeList([s.getType(lhs), s.getType(rhs)]);
            if(s.unify(targs, atypeList([intType(), intType()]))) return intType();
            if(s.unify(targs, atypeList([strType(), strType()]))) return strType();
            s.report(error(current, "No version of + is applicable for %t and %t", lhs, rhs));
            return intType();
        });
     collect(lhs, rhs, c); 
}

void collect(current: (Expression) `<Expression lhs> && <Expression rhs>`, Collector c){
     c.calculateEager("and", current, [lhs, rhs],
        AType (Solver s) {
            s.requireUnify(lhs, boolType(), error(lhs, "Expected `bool`, found %t", lhs));
            s.requireUnify(rhs, boolType(), error(rhs, "Expected `bool`, found %t", rhs));
            return boolType();
        });
    collect(lhs, rhs, c);
}

void collect(current: (Expression) `( <Expression exp> )`, Collector c){
    c.fact(current, exp);
    collect(exp, c);
}

void collect(current: (Expression) `<Id name>`, Collector c){
     c.use(name, {variableId()});
}

void collect(current: (Expression) `<Boolean boolcon>`, Collector c){
     c.fact(current, boolType());
}

void collect(current: (Expression) `<Integer intcon>`, Collector c){
     c.fact(current, intType());
}

