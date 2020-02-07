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