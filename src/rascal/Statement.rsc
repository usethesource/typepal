module rascal::Statement

extend typepal::TypePal;
extend rascal::AType;

import lang::rascal::\syntax::Rascal;
extend rascal::ConvertType;

import rascal::Scope;

// A few statements

void collect(stat: (Statement) `<Expression expression>;`,  Tree scope, FRBuilder frb){
    frb.fact(stat, [expression], AType(){ return typeof(expression); });
}

Tree define(stat: (Statement) `<QualifiedName name> = <Statement statement>`, Tree scope, FRBuilder frb){
    frb.fact(stat, [statement], AType(){ return typeof(statement); });
    frb.define(scope, "<name>", variableId(), name, defLub([statement], AType(){ return typeof(statement); }));
    frb.require("assignment to variable `<name>`", stat, [name, statement],
                () { subtype(typeof(statement), typeof(name), onError(stat, "Incompatible type in assignment to variable `<name>`, found <fmt(statement)>")); });  
    
    return scope;
}

Tree define(stat: (Statement) `<Type tp> <{Variable ","}+ variables>;`, Tree scope, FRBuilder frb){
    <msgs, declaredType> = convertType(tp);
    for(msg <- msgs){
        if(msg is error) frb.reportError(msg.msg, tp);
        if(msg is warning) frb.reportWarning(msg.msg, tp);
    }
    frb.atomicFact(stat, declaredType);
    for(v <- variables){
        frb.define(scope, "<v.name>", variableId(), v, defType(declaredType));
        if(v is initialized){
            frb.require("initialization of variable `<v.name>`", v, [v.initial],
                () { subtype(typeof(v.initial), declaredType, onError(v, "Incompatible type in initialization of `<v.name>`")); });  
        }
    }
    return scope;
}

Tree define(stat: (Statement) `<Label label> if( <{Expression ","}+ conditions> ) <Statement thenPart>`,  Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    condList = [cond | Expression cond <- conditions];
    frb.atomicFact(stat, avalue());
    
    frb.requireEager("if then", stat, condList + [thenPart],
        (){
            for(cond <- condList){
                if(isFullyInstantiated(typeof(cond))){
                    subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
                } else {
                    if(!unify(typeof(cond), abool())){
                        subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
                    }
                }
            }
        });
    return conditions; // thenPart may refer to variables defined in conditions
}

Tree define(stat: (Statement) `<Label label> if( <{Expression ","}+ conditions> ) <Statement thenPart> else <Statement elsePart>`,  Tree scope, FRBuilder frb){
    if(label is \default){
        frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
    }
    condList = [cond | cond <- conditions];
    addElseScope(conditions, elsePart); // variable occurrences in elsePart may not refer to variables defined in conditions
    
    frb.requireEager("if then else", stat, condList + [thenPart, elsePart],
        (){
            for(cond <- condList){
                if(isFullyInstantiated(typeof(cond))){
                    subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
                } else {
                    if(!unify(typeof(cond), abool())){
                        subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
                    }
                }
            }  
            fact(stat, myLUB(typeof(thenPart), typeof(elsePart)));
        });
    return conditions; // thenPart may refer to variables defined in conditions; elsePart may not
}