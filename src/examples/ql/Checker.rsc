module examples::ql::Checker

import examples::ql::Syntax;
extend analysis::typepal::TypePal;

// ----  AType and IdRole ----------------------------------------------------- 

data AType
    = formType(str name) 
    | labelType() 
    | booleanType() 
    | integerType() 
    | stringType() 
    | moneyType() 
    ;

str prettyAType(formType(str name))     = "form <name>";
str prettyAType(labelType())            = "label";
str prettyAType(booleanType())          = "boolean";
str prettyAType(integerType())          = "integer";
str prettyAType(stringType())           = "string";
str prettyAType(moneyType())            = "money";

data IdRole 
    = formId()
    | labelId()
    ;
              
// ---- Collect facts and constraints for QL ----------------------------------

// ---- Form ------------------------------------------------------------------

void collect(current: (Form) `form <Id name> { <Question* questions> }`, Collector c){
    c.define("<name>", formId(), current, defType(formType("<name>")));
    collect(questions, c);
}

// ---- Question --------------------------------------------------------------

void collect(current: (Question) `<Label label> <Var var> : <Type t> <Value? v>`, Collector c){
    c.define("<label>", labelId(), label, defType(labelType()));
    c.define("<var>", variableId(), var, defType(t));
    for((Value) `[<Const const>]` <- v){
        c.requireEqual(const, t, error(const, "Incompatible expression type %t, expected %t", const, t));
        collect(const, c);
    }
    collect(t, c);
}

void collect(current: (Question) `<Label label> <Var var> : <Type t> = <Expr e> <Value? v>`, Collector c){
    c.define("<label>", labelId(), label, defType(labelType()));
    c.define("<var>", variableId(), var, defType(t));
    c.requireEqual(e, t, error(e, "Incompatible expression type %t, expected %t", e, t));
    for((Value) `[<Const const>]` <-  v){
        c.requireEqual(const, t, error(const, "Incompatible expression type %t, expected %t", const, t));
        collect(const, c);
    }
    collect(t, e, c);
}

void collect(current: (Question) `if ( <Expr cond> ) <Question q>`, Collector c){
    c.requireEqual(cond, booleanType(), error(cond, "Condition should be boolean, found %t", cond));
    collect(cond, q, c);
}

void collect(current: (Question) `if ( <Expr cond> ) <Question q1> else <Question q2>`, Collector c){
    c.requireEqual(cond, booleanType(), error(cond, "Condition should be boolean, found %t", cond));
    collect(cond, q1, q2, c);
}

void collect(current: (Question) `{ <Question* questions> }`, Collector c){
    collect(questions, c);
}

void collect(current: (Question) `( <Question* questions> )`, Collector c){
    collect(questions, c);
}

// ---- Expr ------------------------------------------------------------------

void collect(current: (Expr) `<Id name>`, Collector c)
    = c.use(name, {variableId()});

void collect(current: (Expr) `<Boolean boolean>`, Collector c)
   = c.fact(current, booleanType());

void collect(current: (Expr) `<Integer integer>`, Collector c)
   = c.fact(current, integerType());

void collect(current: (Expr) `<String integer>`, Collector c)
   = c.fact(current, stringType());

void collect(current: (Expr) `<Money money>`, Collector c)
   = c.fact(current, moneyType());

void collect(current: (Expr) `( <Expr e> )`, Collector c){
    c.fact(current, e);
    collect(e, c);
}

void collect(current: (Expr) `! <Expr e>`, Collector c){
    c.fact(current, booleanType());
    c.requireEqual(e, booleanType(), error(e, "boolean type expected, found %t", e));
    collect(e, c);
}

void numericOp(Expr e, Expr e1, str op, Expr e2, Collector c){
    c.calculate("numeric operator", e, [e1, e2],
        AType(Solver s){
            t1 = s.getType(e1); t2 = s.getType(e2);
            s.requireTrue({t1,t2} <= {integerType(), moneyType()}, error(e, "Illegal arguments %t and %t for %q", t1, t2, op));
            return (moneyType() in {t1, t2}) ? moneyType() : integerType();
        });
    collect(e1, e2, c);
}

void collect(current: (Expr) `<Expr e1> + <Expr e2>`, Collector c)  = numericOp(current, e1, "+", e2, c);
void collect(current: (Expr) `<Expr e1> - <Expr e2>`, Collector c)  = numericOp(current, e1, "-", e2, c);
void collect(current: (Expr) `<Expr e1> * <Expr e2>`, Collector c)  = numericOp(current, e1, "*", e2, c);
void collect(current: (Expr) `<Expr e1> / <Expr e2>`, Collector c)  = numericOp(current, e1, "/", e2, c);

void comparisonOp(Expr e, Expr e1, str op, Expr e2, Collector c){
    c.calculate("comparison operator", e, [e1, e2],
        AType(Solver s){
            s.requireTrue({s.getType(e1), s.getType(e2)} <= {integerType(), moneyType()},
                          error(e, "Illegal arguments %t and %t for %q", e1, e2, op));
            return booleanType();
         });
    collect(e1, e2, c);
}

void collect(current: (Expr) `<Expr e1> \> <Expr e2>`, Collector c)  = comparisonOp(current, e1, "/\>", e2, c);
void collect(current: (Expr) `<Expr e1> \>= <Expr e2>`, Collector c) = comparisonOp(current, e1, "/\>=", e2, c);
void collect(current: (Expr) `<Expr e1> \< <Expr e2>`, Collector c)  = comparisonOp(current, e1, "/\<", e2, c);
void collect(current: (Expr) `<Expr e1> \<= <Expr e2>`, Collector c) = comparisonOp(current, e1, "/\<=", e2, c);

void equalityOp(Expr e, Expr e1, str op, Expr e2, Collector c){
    c.calculate("(in)equality operator", e, [e1, e2],
        AType(Solver s){
            s.requireEqual(e1, e2, error(e, "Illegal arguments %t and %t for %q", e1, e2, op));
            return booleanType();
         });
    collect(e1, e2, c);
}

void collect(current: (Expr) `<Expr e1> == <Expr e2>`, Collector c) = equalityOp(current, e1, "==", e2, c);
void collect(current: (Expr) `<Expr e1> != <Expr e2>`, Collector c) = equalityOp(current, e1, "!=", e2, c);

void boolOp(Expr e, Expr e1, str op, Expr e2, Collector c){
    c.calculate("boolean operator", e, [e1, e2],
        AType(Solver s){
            s.requireEqual(e1, booleanType(), error(e1, "Illegal argument %t for %q", e1, op));
            s.requireEqual(e2, booleanType(), error(e2, "Illegal argument %t for %q", e2, op));
            return booleanType();
         });
    collect(e1, e2, c);
}

void collect(current: (Expr) `<Expr e1> && <Expr e2>`, Collector c) = boolOp(current, e1, "&&", e2, c);
void collect(current: (Expr) `<Expr e1> || <Expr e2>`, Collector c) = boolOp(current, e1, "||", e2, c);

// ---- Type ------------------------------------------------------------------

void collect(current: Type t, Collector c){
    c.fact(current, ("boolean" : booleanType(), 
                     "integer" : integerType(), 
                     "string"  : stringType(), 
                     "money"   : moneyType())["<t>"]);
}

// ---- Comment ---------------------------------------------------------------
  
void collect(current: (Comment)`<CStart cstart> <CommentChar* commentChars> <CEnd cend>`, Collector c)
    = collect(commentChars, c);

void collect(current: (Embed) `{ <Expr e> }`, Collector c)
    = collect(e, c);