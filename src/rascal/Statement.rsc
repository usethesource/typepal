module rascal::Statement

extend typepal::TypePal;
extend rascal::AType;

import lang::rascal::\syntax::Rascal;
extend rascal::ConvertType;

import rascal::Scope;
import rascal::ATypeExceptions;

// A few statements

// ---- assert

void collect(stat: (Statement) `assert <Expression expression>;`, Tree scope, FRBuilder frb){
    frb.atomicFact(stat, abool());
    frb.require("assert statement", stat, [expression],
        () { subtype(typeof(expression), abool(), onError(expression, "Assertion should be `bool`, found <fmt(expression)>")); });
} 

void collect(stat: (Statement) `assert <Expression expression> : <Expression message> ;`, Tree scope, FRBuilder frb){
   frb.atomicFact(stat, abool());
   frb.require("assert statement with message", stat, [expression, message],
       () { subtype(typeof(expression), abool(), onError(expression, "Assertion should be `bool`, found <fmt(expression)>"));
            subtype(typeof(message), astr(), onError(message, "Assertion message should be `str`, found <fmt(message)>"));
       });
} 
     
// ---- expression
void collect(stat: (Statement) `<Expression expression>;`, Tree scope, FRBuilder frb){
    frb.fact(stat, [expression], AType(){ return typeof(expression); });
}

// ---- visit
Tree define(stat: (Statement) `<Label label> <Visit vst>`, Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    frb.fact(vst, [vst.subject], AType(){ return typeof(vst.subject); });
    return stat;
}

Tree define(pwa: (PatternWithAction) `<Pattern pattern> =\> <Replacement replacement>`,  Tree scope, FRBuilder frb){
    frb.require("pattern replacement", pwa, [pattern, replacement],
        (){ subtype(typeof(replacement), typeof(pattern), onError(pwa, "A pattern of type <fmt(pattern)> cannot be replaced by <fmt(replacement)>")); });
    return pwa;
}


Tree define(pwa: (PatternWithAction) `<Pattern pattern>: <Statement statement>`,  Tree scope, FRBuilder frb){
    for(Expression expr <- getInsertExpressions(statement)){
            frb.requireEager("insert expression", expr, [expr, pattern], makeInsertRequirement(expr, pattern));     
        }
    return pwa;
}

// TODO: finds too many (nested) inserts!
// TODO: check that insert occurs inside a replacement context
list[Expression] getInsertExpressions(Tree stat)
    = [expr | /(Statement) `insert <Expression expr>;` := stat];

// Note: Rascal's closures are mutable, therefore we need an extra closure when creating
// several requirements from the same function context. In this way the value of expr becomes fixed
void() makeInsertRequirement(Expression expr, Pattern pat)
       = () { 
             if(isFullyInstantiated(typeof(expr)) && isFullyInstantiated(typeof(pat))){
                subtype(typeof(expr), typeof(pat), onError(expr, "Insert type should be subtype of <fmt(pat)>, found <fmt(expr)>"));
              } else {
              if(!unify(typeof(expr), patType)){
                 subtype(typeof(expr), patType, onError(expr, "Insert type should be subtype of <fmt(patType)>, found <fmt(expr)>"));
              }
           }
         };

// --- while

Tree define(stat: (Statement) `<Label label> while( <{Expression ","}+ conditions> ) <Statement body>`,  Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    condList = [cond | Expression cond <- conditions];
    frb.atomicFact(stat, avalue());
    
    frb.requireEager("while statement", stat, condList + [body], (){ checkConditions(condList); });
    return conditions; // body may refer to variables defined in conditions
}

void checkConditions(list[Expression] condList){
    for(Expression cond <- condList){
        if(isFullyInstantiated(typeof(cond))){
            subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
        } else {
            if(!unify(typeof(cond), abool())){
                subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
            }
        }
    }
}

// ---- do

Tree define(stat: (Statement) `<Label label> do <Statement body> while ( <Expression condition> ) ;`, Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    condList = [cond | Expression cond <- conditions];
    frb.atomicFact(stat, avalue());
    
    frb.requireEager("do statement", stat, condList + [body], (){ checkConditions(condList); });
    return stat; // condition may refer to variables defined in body
}

//---- for

Tree define(stat: (Statement) `<Label label> for( <{Expression ","}+ conditions> ) <Statement body>`,  Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    condList = [cond | Expression cond <- conditions];
    frb.atomicFact(stat, avalue());
    
    frb.requireEager("for statement", stat, condList + [body], (){ checkConditions(condList); });
    return conditions; // body may refer to variables defined in conditions
}

// ---- if

Tree define(stat: (Statement) `<Label label> if( <{Expression ","}+ conditions> ) <Statement thenPart>`,  Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    condList = [cond | Expression cond <- conditions];
    frb.atomicFact(stat, avalue());
    
    frb.requireEager("if then", stat, condList + [thenPart], (){ checkConditions(condList); });
    return conditions; // thenPart may refer to variables defined in conditions
}

// --- if then else

Tree define(stat: (Statement) `<Label label> if( <{Expression ","}+ conditions> ) <Statement thenPart> else <Statement elsePart>`,  Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    condList = [cond | cond <- conditions];
    addElseScope(conditions, elsePart); // variable occurrences in elsePart may not refer to variables defined in conditions
    
    frb.calculateEager("if then else", stat, condList + [thenPart, elsePart],
        AType (){
            checkConditions(condList);
            return myLUB(typeof(thenPart), typeof(elsePart));
        });
    return conditions; // thenPart may refer to variables defined in conditions; elsePart may not
}

// ---- switch
// ---- fail
// ---- break
// ---- continue
// ---- filter
// ---- solve
// ---- try
// ---- try finally
// ---- non-empty block
// ---- empty block
// ---- assignment

Tree define(stat: (Statement) `<QualifiedName name> = <Statement statement>`, Tree scope, FRBuilder frb){
    frb.fact(stat, [statement], AType(){ return typeof(statement); });
    frb.define(scope, "<name>", variableId(), name, defLub([statement], AType(){ return typeof(statement); }));
    frb.require("assignment to variable `<name>`", stat, [name, statement],
                () { subtype(typeof(statement), typeof(name), onError(stat, "Incompatible type in assignment to variable `<name>`, found <fmt(statement)>")); });  
    
    return scope;
}

// ---- return
// ---- throw
// ---- insert
// ---- append
// ---- function declaration
// ---- local variable declaration

// ---- local variable declaration

Tree define(stat: (Statement) `<Type tp> <{Variable ","}+ variables>;`, Tree scope, FRBuilder frb){
    declaredType = convertType(tp, frb);
    declaredTypeVars = collectTypeVars(declaredType);
    AType tau = declaredType;
    if(isEmpty(declaredTypeVars)){
       frb.atomicFact(stat, declaredType);
    } else {
       if(size([v | v <- variables]) > 1){
          frb.reportError(stat, "Parameterized declared type not allowed with multiple initializations");
       }
       tau = frb.newTypeVar(scope);
    }
    
    for(v <- variables){
        if(v is initialized){
            frb.define(scope, "<v.name>", variableId(), v, defType(tau)); 
            if(isEmpty(declaredTypeVars)){ 
               frb.calculate("initialization of variable `<v.name>`", v, [v.initial],   
                   AType (){ 
                       initialType = typeof(v.initial); 
                       initialTypeVars = collectTypeVars(initialType);
                       if(!isEmpty(initialTypeVars)){
                          try {
                            Bindings bindings = match(declaredType, initialType, ());
                            initialType = instantiate(initialType, bindings, v);
                          } catch invalidMatch(t1, t2): {
                            reportError(v, "Cannot match types <fmt(t1)> and <fmt(t2)>");
                            return avalue();
                          } catch invalidMatch(str pname, AType actual, AType bound): {
                            reportError(v, "Type parameter <fmt(pname)> should be less than <fmt(bound)>, but is bound to <fmt(actual)>");
                            return avalue();
                          } catch invalidInstantiation():
                            return avalue();
                       }
                       subtype(initialType, declaredType, onError(v, "Incompatible type in initialization of <fmt("<v.name>")>"));
                       return declaredType;                  
                   });
            } else {
               frb.calculate("initialization of variable `<v.name>`", v.name, [v.initial],
                   AType () { 
                       initialType = typeof(v.initial); 
                       initialTypeVars = collectTypeVars(initialType);
                       try {
                         Bindings bindings = match(declaredType, initialType, ());
                         declaredType = instantiate(declaredType, bindings, v);
                         initialType = instantiate(initialType, bindings, v);
                       } catch invalidMatch(t1, t2): {
                         reportError(v, "Cannot match types <fmt(t1)> and <fmt(t2)>");
                         return avalue();
                       } catch invalidMatch(str pname, AType actual, AType bound): {
                         reportError(v, "Type parameter <fmt(pname)> should be less than <fmt(bound)>, but is bound to <fmt(actual)>");
                         return avalue();
                       } catch invalidInstantiation():
                            return avalue();
                       
                       unify(tau, declaredType);   // bind tau to instantiated declaredType
                       subtype(initialType, declaredType, onError(v, "Incompatible type in initialization of <fmt("<v.name>")>"));
                       return declaredType;
                   }); 
            } 
        }
    }
    return scope;
}
