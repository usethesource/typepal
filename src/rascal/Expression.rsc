module rascal::Expression

extend typepal::TypePal;

import rascal::AType;
import rascal::ATypeUtils;
import rascal::Scope;

import lang::rascal::\syntax::Rascal;


// Check the types of Rascal literals
void collect(Literal l:(Literal)`<IntegerLiteral il>`, Tree scope, FRBuilder frb){
    frb.atomicFact(il, aint());
}

void collect(Literal l:(Literal)`<RealLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, areal());
}

void collect(Literal l:(Literal)`<BooleanLiteral bl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, abool());
 }

void collect(Literal l:(Literal)`<DateTimeLiteral dtl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, adatetime());
}

void collect(Literal l:(Literal)`<RationalLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, arat());
}

//void collect(Literal l:(Literal)`<RegExpLiteral rl>`, Configuration c) {

void collect(Literal l:(Literal)`<StringLiteral sl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, astr());
}

void collect(Literal l:(Literal)`<LocationLiteral ll>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, aloc());
}

// A few expressions

void collect(exp: (Expression) `<QualifiedName name>`, Tree scope, FRBuilder frb){
    frb.use(scope, name, {variableId(), formalId(), functionId(), constructorId()});
}

void collect(exp: (Expression) `{ <Statement+ statements> }`, Tree scope, FRBuilder frb){
    stats = [ stat | Statement stat <- statements ];
    frb.calculate("non-empty block", exp, stats,
        AType() { return typeof(stats[-1]); }
        );
}

void collect(exp: (Expression) `<Expression exp1> + <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.calculate("`+` operator", exp, [exp1, exp2], 
        AType() {
            t1 = typeof(exp1); t2 = typeof(exp2);
            if(t1 in numericTypes && t2 in numericTypes){
               return myLUB(t1, t2);
            }
            switch([t1, t2]){
                case [alist(e1), x]: return alist(e2) := x ? alist(getLUB(e1, e2)) : alist(myLUB(e1, x));
                case [aset(e1), x]: return aset(e2) := x ? aset(myLUB(e1, e2)) : aset(myLUB(e1, x));
                //case [\map(e1a, e2a), \map(e1b, e2b)]: return rascalType(\map(lub(e1a,e1b), lub(e2a,e2b)));
                //case [\tuple(e1), \tuple(e2)]: return rascalType(\tuple(lub(e1, e2)));
                case [astr(), astr()]: return astr();
                case [aloc(), astr()]: return aloc();       
            }
            if(alist(e2) := t2){
                return alist(myLUB(t1, e2));
            }
            if(aset(e2) := t2){
                return aset(myLUB(t1, e2));
            }
                
             reportError(exp, "No version of `+` is applicable for <fmt(exp1)> and <fmt(exp2)>");    
      }); 
}

Tree define(exp: (Expression) `<Expression exp1> || <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, abool());
      
    frb.requireEager("`||` operator", exp, [exp1, exp2],
        (){ if(!unify(abool(), typeof(exp1))) reportError(exp1, "Argument of || should be `bool`, found <fmt(exp1)>");
            if(!unify(abool(), typeof(exp2))) reportError(exp2, "Argument of || should be `bool`, found <fmt(exp2)>");
            // TODO: check that exp1 and exp2 introduce the same set of variables
          });
    return scope;
}

Tree define(exp: (Expression) `<Expression exp1> && <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, abool());
   
    frb.requireEager("`&&` operator", exp, [exp1, exp2],
        (){ if(!unify(abool(), typeof(exp1))) reportError(exp1, "Argument of && should be `bool`, found <fmt(exp1)>");
            if(!unify(abool(), typeof(exp2))) reportError(exp2, "Argument of && should be `bool`, found <fmt(exp2)>");
          });
    return scope;
}

void collect(exp: (Expression) `<Expression exp1> == <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, abool());
    frb.require("`==` operator", exp, [exp1, exp2],
        (){ comparable(typeof(exp1), typeof(exp2), onError(exp, "`==` operator not defined for <fmt(exp1)> and <fmt(exp2)>"));
          });
}

void collect(exp: (Expression) `[ <{Expression ","}* elements0> ]`, Tree scope, FRBuilder frb){
    elms = [ e | Expression e <- elements0 ];
    frb.calculateEager("list expression", exp, elms,
        AType() { return alist(lub([typeof(elm) | elm <- elms])); });
}

void collect(exp: (Expression) `{ <{Expression ","}* elements0> }`, Tree scope, FRBuilder frb){
    elms = [ e | Expression e <- elements0 ];
    frb.calculateEager("set expression", exp, elms,
        AType() { return aset(lub([typeof(elm) | elm <- elms])); });
}

void collect(exp: (Expression) `\< <{Expression ","}* elements1> \>`, Tree scope, FRBuilder frb){
    elms = [ e | Expression e <- elements1 ];
    frb.calculateEager("tuple expression", exp, elms,
        AType() {
                return atuple(atypeList([ typeof(elm) | elm <- elms ]));
        });
}

void collect(exp: (Expression) `( <{Mapping[Expression] ","}* mappings>)`, Tree scope, FRBuilder frb){
    froms = [ m.from | m <- mappings ];
    tos =  [ m.to | m <- mappings ];
    frb.calculateEager("map expression", exp, froms + tos,
        AType() {
                return amap(lub([ typeof(f) | f <- froms ]), lub([ typeof(t) | t <- tos ]));
        });
}

void collect(exp: (Expression) `<Pattern pat> := <Expression expression>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, abool());
    if(pat is  qualifiedName){
        name = pat.qualifiedName;
        frb.define(scope, "<name>", variableId(), name, defLub([expression], AType(){ return typeof(expression); }));
        frb.require("match variable `<name>`", exp, [name, expression],
                () { comparable(typeof(expression), typeof(name), onError(exp, "Incompatible type in match using `<name>`")); });  
    } else {
        frb.requireEager("`:=` operator", exp, [pat, expression],
            () { ptype = typeof(pat); etype = typeof(expression);
                 if(isFullyInstantiated(ptype) && isFullyInstantiated(etype)){
                    comparable(ptype, etype, onError(exp, "Cannot match <fmt(pat)> pattern with <fmt(expression)> subject"));
                 } else {
                    unify(ptype, etype, onError(pat, "Type of pattern could not be computed"));
                    // add comparable?
                 }
                 fact(pat, typeof(pat));
               });
    }
}


void checkKwArgs(list[Keyword] kwFormals, keywordArguments){
    if(keywordArguments is none) return;
 
    next_arg:
    for(kwa <- keywordArguments.keywordArgumentList){ 
        kwName = "<kwa.name>";
        kwType = typeof(kwa.expression);
        for(<ft, fn, de> <- kwFormals){
           if(kwName == fn){
              if(!comparable(kwType, ft)){
                reportError(kwa, "Keyword argument <fmt(kwName)> has type <fmt(kwType)>, expected <fmt(ft)>");
              }
              continue next_arg;
           } 
        }
        
        reportError(kwa, "Undefined keyword argument <fmt(kwName)>; <kwFormals<0,1>>");
    }
 } 

list[Keyword] getCommonKeywords(aadt(str adtName, list[AType] parameters, list[Keyword] common)) =  common;
list[Keyword] getCommonKeywords(overloadedAType(rel[Key, AType] overloads)) = [ *getCommonKeywords(adt) | <def, adt> <- overloads ];
                  

void collect(callOrTree: (Expression) `<Expression expression> ( <{Expression ","}* arguments> <KeywordArguments[Expression] keywordArguments>)`, Tree scope, FRBuilder frb){
    actuals = [a | Expression a <- arguments];
    
    frb.calculate("call", callOrTree, expression + actuals,
        AType(){        
            if(overloadedAType(rel[Key, AType] overloads) := typeof(expression)){
              next_fun:
                for(<key, tp> <- overloads){                       
                    if(afunc(AType ret, atypeList(list[AType] formals), list[Keyword] kwFormals) := tp){
                        nactuals = size(actuals); nformals = size(formals);
                        if(nactuals != nformals){
                            continue next_fun;
                        }
                        for(int i <- index(actuals)){
                            if(!comparable(typeof(actuals[i]), formals[i])) continue next_fun;
                        }
                        checkKwArgs(kwFormals, keywordArguments);
                        return ret;
                    }
                 }
               next_cons:
                 for(<key, tp> <- overloads){
                    if(acons(aadt(adtName, list[AType] parameters, list[Keyword] common), str consName, list[Field] fields, list[Keyword] kwFields) := tp){
                        nactuals = size(actuals); nformals = size(fields);
                        if(nactuals != nformals) continue next_cons;
                        for(int i <- index(actuals)){
                            if(!comparable(typeof(actuals[i]), fields[i].fieldType)) continue next_cons;
                        }
                        adtType = typeof(adtName, scope, {dataId()});
                        checkKwArgs(kwFields + getCommonKeywords(adtType), keywordArguments);
                        return adtType;
                    }
                }
                reportError(callOrTree, "No function or constructor <fmt(expression)> for arguments <fmt(actuals)>");
            }
          
            if(afunc(AType ret, atypeList(list[AType] formals), list[Keyword] kwFormals) := typeof(expression)){
                nactuals = size(actuals); nformals = size(formals);
                if(nactuals != nformals){
                    reportError(callOrTree, "Expected <nformals> argument<nformals != 1 ? "s" : ""> for `<"<expression>">`, found <nactuals>");
                }
                for(int i <- index(actuals)){
                    comparable(typeof(actuals[i]), formals[i], onError(actuals[i], "Argument of `<"<expression>">` should have type <fmt(formals[i])>, found <fmt(actuals[i])>"));
                }
                checkKwArgs(kwFormals, keywordArguments);
                return ret;
            }
            if(acons(aadt(adtName, list[AType] parameters, list[Keyword] common), str consName, list[Field] fields, list[Keyword] kwFields) := typeof(expression)){
                nactuals = size(actuals); nformals = size(fields);
                if(nactuals != nformals){
                    reportError(callOrTree, "Expected <nformals> argument<nformals != 1 ? "s" : ""> for `<"<expression>">`, found <nactuals>");
                }
                for(int i <- index(actuals)){
                    comparable(typeof(actuals[i]), fields[i].fieldType, onError(actuals[i], "Field should have type <fmt(fields[i].fieldType)>, found <fmt(actuals[i])>"));
                }
                adtType = typeof(adtName, scope, {dataId()});
                checkKwArgs(kwFields + getCommonKeywords(adtType), keywordArguments);
                return adtType;
            }
            reportError(callOrTree, "Function or constructor type required for <fmt(expression)>, found <fmt(expression)>");
        });
}
