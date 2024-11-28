@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::calc::Checker

import examples::calc::Syntax;                    // The Calc syntax
extend analysis::typepal::TypePal;          // TypePal

// ----  Extend AType --------------------------------------------------------- 

data AType   
    = boolType()    
    | intType()                                     
    ;
    
str prettyAType(boolType()) = "bool";
str prettyAType(intType()) = "int";

// ---- collect constraints for Calc ------------------------------------------

void collect(current: (Decl) `var <Id name> = <Exp exp> ;`, Collector c){
    c.define("<name>", variableId(), current, defType(exp));
    collect(exp, c);
} 

void collect(current: (Exp) `<Id name>`, Collector c){
    c.use(name, {variableId()});
}

void collect(current: (Exp) `<Boolean boolean>`, Collector c){
    c.fact(current, boolType());
}

void collect(current: (Exp) `<Integer integer>`, Collector c){
    c.fact(current, intType());
}

void collect(current: (Exp) `( <Exp e> )`, Collector c){
    c.fact(current, e);
    collect(e, c);
}

void collect(current: (Exp) `<Exp e1> + <Exp e2>`, Collector c){
     c.calculate("addition", current, [e1, e2],
        AType (Solver s) { 
            switch(<s.getType(e1), s.getType(e2)>){
                case <intType(), intType()>: return intType();
                case <boolType(), boolType()>: return boolType();
                default: {
                    s.report(error(current, "`+` not defined for %t and %t", e1, e2));
                    return intType();
                  }
            }
        });
      collect(e1, e2, c);
}

void collect(current: (Exp) `<Exp e1> * <Exp e2>`, Collector c){
     c.calculate("multiplication", current, [e1, e2],
        AType (Solver s) { 
            switch(<s.getType(e1), s.getType(e2)>){
                case <intType(), intType()>: return intType();
                case <boolType(), boolType()>: return boolType();
                default: {
                    s.report(error(current, "`*` not defined for %t and %t", e1, e2));
                    return intType();
                  }
            }
        });
      collect(e1, e2, c);
}

void collect(current: (Exp) `if <Exp cond> then <Exp e1> else <Exp e2>`, Collector c){
    c.calculate("if Exp", current, [cond, e1, e2],
        AType(Solver s){
            s.requireEqual(cond, boolType(),
                           error(cond, "Condition should be Boolean, found %t", cond));
            s.requireEqual(e1, e2, 
                           error(current, "Equal types required, found %t and %t", e1, e2));
            return s.getType(e1);
        });
    collect(cond, e1, e2, c);
}