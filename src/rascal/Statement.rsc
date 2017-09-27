module rascal::Statement

extend typepal::TypePal;
extend rascal::AType;

import lang::rascal::\syntax::Rascal;
extend rascal::ConvertType;

import rascal::Scope;
import rascal::ATypeExceptions;

// A few statements

// ---- assert

void collect(stat: (Statement) `assert <Expression expression>;`, FRBuilder frb){
    frb.atomicFact(stat, abool());
    frb.require("assert statement", stat, [expression],
        () { subtype(typeof(expression), abool(), onError(expression, "Assertion should be `bool`, found <fmt(expression)>")); });
    collectParts(stat, frb);
} 

void collect(stat: (Statement) `assert <Expression expression> : <Expression message> ;`, FRBuilder frb){
   frb.atomicFact(stat, abool());
   frb.require("assert statement with message", stat, [expression, message],
       () { subtype(typeof(expression), abool(), onError(expression, "Assertion should be `bool`, found <fmt(expression)>"));
            subtype(typeof(message), astr(), onError(message, "Assertion message should be `str`, found <fmt(message)>"));
       });
   collectParts(stat, frb);
} 
     
// ---- expression
void collect(stat: (Statement) `<Expression expression>;`, FRBuilder frb){
    frb.fact(stat, [expression], AType(){ return typeof(expression); });
    collectParts(stat, frb);
}

// ---- visit
void collect(stat: (Statement) `<Label label> <Visit vst>`, FRBuilder frb){
    frb.enterScope(visitScope(), stat);
        if(label is \default){
            frb.define("<label.name>", labelId(), label.name, noDefInfo());
        }
        frb.fact(vst, [vst.subject], AType(){ return typeof(vst.subject); });
        collectParts(stat, frb);
    frb.leaveScope(visitScope(), stat);
}

void collect(pwa: (PatternWithAction) `<Pattern pattern> =\> <Replacement replacement>`,  FRBuilder frb){
    frb.enterScope(replacementScope(), pwa);
        frb.setScopeInfo(pattern);
        frb.require("pattern replacement", pwa, [pattern, replacement],
            (){ subtype(typeof(replacement), typeof(pattern), onError(pwa, "A pattern of type <fmt(pattern)> cannot be replaced by <fmt(replacement)>")); });
        collectParts(pwa, frb);
    frb.leaveScope(replacementScope(), pwa);
}

void collect(pwa: (PatternWithAction) `<Pattern pattern>: <Statement statement>`,  FRBuilder frb){
    frb.enterScope(replacementScope(), pwa);
        frb.setScopeInfo(pattern);
        collectParts(pwa, frb);
    frb.leaveScope(replacementScope(), pwa);
}

void collect(stat: (Statement) `insert <Expression expr>;`, FRBuilder frb){
    <found, scope, scopeInfo> = frb.getScopeInfo(replacementScope());
    if(!found){
        frb.reportError(stat, "Insert found outside replacement context");
    } else {
      if(Pattern pat := scopeInfo){
         frb.requireEager("insert expression", expr, [expr, pat], 
             () { 
                  if(isFullyInstantiated(typeof(expr)) && isFullyInstantiated(typeof(pat))){
                     subtype(typeof(expr), typeof(pat), onError(expr, "Insert type should be subtype of <fmt(pat)>, found <fmt(expr)>"));
                  } else {
                  if(!unify(typeof(expr), patType)){
                     subtype(typeof(expr), patType, onError(expr, "Insert type should be subtype of <fmt(patType)>, found <fmt(expr)>"));
                  }
                }
             });
      } else {
        throw "Inconsistent info from replacement scope: <info>";
      }
    }
    collectParts(stat, frb);
}

// --- while

void collect(stat: (Statement) `<Label label> while( <{Expression ","}+ conditions> ) <Statement body>`,  FRBuilder frb){
    frb.enterScope(conditionalScope(), conditions);   // body may refer to variables defined in conditions
        if(label is \default){
            frb.define("<label.name>", labelId(), label.name, noDefInfo());
        }
        condList = [cond | Expression cond <- conditions];
        frb.atomicFact(stat, avalue());
        
        frb.requireEager("while statement", stat, condList + [body], (){ checkConditions(condList); });
        collectParts(stat, frb);
    frb.leaveScope(conditionalScope(), conditions);
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

void collect(stat: (Statement) `<Label label> do <Statement body> while ( <Expression condition> ) ;`, FRBuilder frb){
    frb.enterScope(conditionalScope(), stat);   // condition may refer to variables defined in body
        if(label is \default){
            frb.define(stat, "<label.name>", labelId(), label.name, noDefInfo());
        }
        condList = [cond | Expression cond <- conditions];
        frb.atomicFact(stat, avalue());
        
        frb.requireEager("do statement", stat, condList + [body], (){ checkConditions(condList); });
        collectParts(stat, frb);
    frb.leaveScope(conditionalScope(), stat); 
}

//---- for

void collect(stat: (Statement) `<Label label> for( <{Expression ","}+ conditions> ) <Statement body>`,  FRBuilder frb){
    frb.enterScope(conditionalScope(), conditions);   // body may refer to variables defined in conditions
        if(label is \default){
            frb.define("<label.name>", labelId(), label.name, noDefInfo());
        }
        condList = [cond | Expression cond <- conditions];
        frb.atomicFact(stat, avalue());
        
        frb.requireEager("for statement", stat, condList + [body], (){ checkConditions(condList); });
        collectParts(stat, frb);
    frb.leaveScope(conditionalScope(), conditions);  
}

// ---- if

void collect(stat: (Statement) `<Label label> if( <{Expression ","}+ conditions> ) <Statement thenPart>`,  FRBuilder frb){
    frb.enterScope(conditionalScope(), conditions); // thenPart may refer to variables defined in conditions
        if(label is \default){
            frb.define("<label.name>", labelId(), label.name, noDefInfo());
        }
        condList = [cond | Expression cond <- conditions];
        frb.atomicFact(stat, avalue());
        
        frb.requireEager("if then", stat, condList + [thenPart], (){ checkConditions(condList); });
        collectParts(stat, frb);
    frb.leaveScope(conditionalScope(), conditions);   
}

// --- if then else

void collect(stat: (Statement) `<Label label> if( <{Expression ","}+ conditions> ) <Statement thenPart> else <Statement elsePart>`,  FRBuilder frb){
    frb.enterScope(conditionalScope(), conditions);   // thenPart may refer to variables defined in conditions; elsePart may not
        if(label is \default){
            frb.define("<label.name>", labelId(), label.name, noDefInfo());
        }
        condList = [cond | cond <- conditions];
        addElseScope(conditions, elsePart); // variable occurrences in elsePart may not refer to variables defined in conditions
        
        frb.calculateEager("if then else", stat, condList + [thenPart, elsePart],
            AType (){
                checkConditions(condList);
                return myLUB(typeof(thenPart), typeof(elsePart));
            });
    collectParts(stat, frb);
    frb.leaveScope(conditionalScope(), conditions); 
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

void collect(stat: (Statement) `<Label label> { <Statement+ statements> }`, FRBuilder frb){
    if(label is \default){
       frb.define("<label.name>", labelId(), label.name, noDefInfo());
    }
    collectParts(stat, frb);
}

// ---- empty block
// ---- assignment

void collect(stat: (Statement) `<QualifiedName name> = <Statement statement>`, FRBuilder frb){
    frb.fact(stat, [statement], AType(){ return typeof(statement); });
    frb.define("<name>", variableId(), name, defLub([statement], AType(){ return typeof(statement); }));
    frb.require("assignment to variable `<name>`", stat, [name, statement],
                () { subtype(typeof(statement), typeof(name), onError(stat, "Incompatible type in assignment to variable `<name>`, found <fmt(statement)>")); });  
    collectParts(stat, frb);
}

// ---- return
// ---- throw
// ---- insert
// ---- append
// ---- function declaration
// ---- local variable declaration

// ---- local variable declaration

void collect(stat: (Statement) `<Type tp> <{Variable ","}+ variables>;`, FRBuilder frb){
    declaredType = convertType(tp, frb);
    declaredTypeVars = collectTypeVars(declaredType);
    AType tau = declaredType;
    if(isEmpty(declaredTypeVars)){
       frb.atomicFact(stat, declaredType);
    } else {
       if(size([v | v <- variables]) > 1){
          frb.reportError(stat, "Parameterized declared type not allowed with multiple initializations");
       }
       tau = frb.newTypeVar();
    }
    
    for(v <- variables){
        if(v is initialized){
            frb.define("<v.name>", variableId(), v, defType(tau)); 
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
    collectParts(stat, frb);
}
