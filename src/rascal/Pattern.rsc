module rascal::Pattern

extend typepal::TypePal;

import lang::rascal::\syntax::Rascal;
extend rascal::AType;
extend rascal::ATypeUtils;
import rascal::Scope;
import rascal::ConvertType;
import lang::rascal::types::AbstractName;

// A few patterns

void collect(Pattern pat:(Literal)`<IntegerLiteral il>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, aint());
}

void collect(Pattern pat:(Literal)`<RealLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, areal());
}

void collect(Pattern pat:(Literal)`<BooleanLiteral bl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, abool());
 }

void collect(Pattern pat:(Literal)`<DateTimeLiteral dtl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, adatetime());
}

void collect(Pattern pat:(Literal)`<RationalLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, arat());
}

//void collect(Literalpat:(Literal)`<RegExpLiteral rl>`, Configuration c) {

void collect(Pattern pat:(Literal)`<StringLiteral sl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, astr());
}

void collect(Pattern pat:(Literal)`<LocationLiteral ll>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, aloc());
}
            
Tree define(Pattern pat: (Pattern) `<Type tp> <Name name>`, Tree scope, FRBuilder frb){
    <msgs, declaredType> = convertType(tp);
    for(msg <- msgs){
        if(msg is error) frb.reportError(msg.msg, tp);
        if(msg is warning) frb.reportWarning(msg.msg, tp);
    }
    frb.atomicFact(pat, declaredType);
    frb.define(scope, "<name>", variableId(), name, defType(declaredType));
    return scope;
}

void handleSingleVariablePatterns(list[Pattern] pats, Tree scope, FRBuilder frb){
    for(pat <- pats){
        if(namePat: (Pattern) `<QualifiedName name>` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return typeof(tau); }));
        }
        if(splicePat: (Pattern) `*<QualifiedName name>` := pat || splicePat: (Pattern) `<QualifiedName name>*` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return alist(typeof(tau)); }));
        }
        if(splicePlusPat: (Pattern) `+<QualifiedName name>` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return alist(typeof(tau)); }));
        }
    }
}

void collect(listPat: (Pattern) `[ <{Pattern ","}* elements0> ]`, Tree scope, FRBuilder frb){
    pats = [ p | Pattern p <- elements0 ];
   
    handleSingleVariablePatterns(pats, scope, frb);
    
    tvElm = frb.newTypeVar(scope);
    frb.calculateEager("list pattern", listPat, pats, 
        AType() { 
            elmType = lub([typeof(pat) | pat <- pats]);
            listPatType = alist(lub([typeof(pat) | pat <- pats]));
            unify(alist(tvElm), listPatType); // bind type variable to elmType
            return alist(tvElm);
        });
}

void collect(setPat: (Pattern) `{ <{Pattern ","}* elements0> }`, Tree scope, FRBuilder frb){
    pats = [ p | Pattern p <- elements0 ];
   
    handleSingleVariablePatterns(pats, scope, frb);
    
    tvElm = frb.newTypeVar(scope);
    frb.calculateEager("set pattern", setPat, pats, 
        AType() { 
            elmType = lub([typeof(pat) | pat <- pats]);
            setPatType = aset(lub([typeof(pat) | pat <- pats]));
            unify(aset(tvElm), setPatType); // bind type variable to elmType
            return aset(tvElm);
        });
}

void collect(tuplePat: (Pattern) `\< <{Pattern ","}+ elements1> \>`, Tree scope, FRBuilder frb){
    pats = [ p | Pattern p <- elements1 ];
    for(pat <- pats){
        if(namePat: (Pattern) `<QualifiedName name>` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return typeof(tau); }));
        }
    }
    
    frb.calculateEager("tuple pattern", tuplePat, pats, 
        AType() { return atuple(atypeList([typeof(pat) | pat <- pats])); });
}

void collect(callOrTreePat: (Pattern) `<Pattern expression> ( <{Pattern ","}* arguments> <KeywordArguments[Pattern] keywordArguments> )`, Tree scope, FRBuilder frb){
    
    if(namePat: (Pattern) `<QualifiedName name>` := expression){
        frb.use(scope, name, {variableId(), formalId(), constructorId()});
    }
    
    pats = [ p | Pattern p <- arguments ];
    for(pat <- pats){
        if(namePat: (Pattern) `<QualifiedName name>` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return typeof(tau); }));
        }
    }
    
    frb.calculateEager("call or tree pattern", callOrTreePat, pats,
        AType(){        
            if(overloadedAType(rel[Key, AType] overloads) := typeof(expression)){
              
               next_cons:
                 for(<key, tp> <- overloads){
                    if(acons(str adtName, str consName, lrel[AType fieldType, str fieldName] fields, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields) := tp){
                        nactuals = size(fields); nformals = size(fields);
                        if(nactuals != nformals) continue next_cons;
                        for(int i <- index(fields)){
                            if(isFullyInstantiated(typeof(pats[i]))){
                               if(!comparable(typeof(pats[i]), fields[i].fieldType)) continue next_cons;
                            } else {
                               if(!unify(typeof(pats[i]), fields[i].fieldType)) continue next_cons;
                            }  
                        }
                        checkKwArgs(kwFields, keywordArguments);
                        return aadt(adtName);
                    }
                }
                reportError(callOrTreePat, "No function or constructor <"<expression>"> for arguments <fmt(pats)>");
            }
        
            if(acons(str adtName, str consName, lrel[AType fieldType, str fieldName] fields, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields) := typeof(expression)){
                nactuals = size(pats); nformals = size(fields);
                if(nactuals != nformals){
                    reportError(callOrTreePat, "Expected <nformals> argument<nformals != 1 ? "s" : ""> for `<expression>`, found <nactuals>");
                }
                for(int i <- index(pats)){
                    if(isFullyInstantiated(typeof(pats[i]))){
                        comparable(typeof(pats[i]), fields[i].fieldType, onError(pats[i], "Field <fmt(fields[i].fieldName)> should have type <fmt(fields[i].fieldType)>, found <fmt(pats[i])>"));
                    } else {
                        unify(typeof(pats[i]), fields[i].fieldType, onError(pats[i], onError(pats[i], "Field <fmt(fields[i].fieldName)> should have type <fmt(fields[i].fieldType)>, found <fmt(pats[i])>")));
                    }
                }
                checkKwArgs(kwFields, keywordArguments);
                return aadt(adtName);
            }
            reportError(callOrTreePat, "Function or constructor type required for <"<expression>">, found <fmt(expression)>");
        });
}

Tree define(varBecomesPat: (Pattern) `<Name name> : <Pattern pattern>`, Tree scope, FRBuilder frb){
    frb.define(scope, "<name>", variableId(), name, defLub([pattern], AType() { return typeof(pattern); }));
    frb.calculateEager("variable becomes", varBecomesPat, [pattern], AType(){ return typeof(pattern); });
    return scope;
}

Tree define(varBecomesPat: (Pattern) `<Type tp> <Name name> : <Pattern pattern>`, Tree scope, FRBuilder frb){
    declaredType = toAType(convertType(tp));
    frb.define(scope, "<name>", variableId(), name, defType(declaredType));
    frb.atomicFact(varBecomesPat, declaredType);
    tau = frb.newTypeVar(scope);
    frb.atomicFact(pattern, tau);
    frb.requireEager("typed variable becomes", varBecomesPat, [pattern],
        () { subtype(typeof(pattern), declaredType, onError(pattern, "Incompatible type in assignment to variable `<name>`, expected <fmt(declaredType)>, found <fmt(pattern)>"));
        });
    return scope;
}

void collect(descendantPat: (Pattern) `/ <Pattern pattern>`, Tree scope, FRBuilder frb){
    frb.atomicFact(descendantPat, avalue());
}

//TODO: negative 
//TODO: map
//TODO: reifiedType
//TODO: asType
//TODO: anti
