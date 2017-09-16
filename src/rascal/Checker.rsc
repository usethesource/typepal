@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module rascal::Checker

import IO;
import String;
import util::Benchmark;

import lang::rascal::\syntax::Rascal;
import Type;
import lang::rascal::types::ConvertType;
import lang::rascal::types::AbstractType;

extend typepal::TypePal;
extend typepal::TestFramework;

data AType 
    =  aint()
     | abool()
     | areal()
     | arat()
     | astr()
     | anum()
     | anode()
     | avoid()
     | avalue()
     | aloc()
     | adatetime()
     | alist(AType elmType)
     | aset(AType elmType)
     | atuple(AType elemType)
     | amap(AType keyType, AType valType)
     | arel(AType elemType)
     | alrel(AType elemType)
     | afunc(AType ret, list[AType] formals, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals)
     | aadt(str adtName)
     | acons(str adtName, str consName, 
             lrel[AType fieldType, str fieldName] fields, 
             lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields)
     ;
    
Symbol toSymbol(aint()) = \int();
Symbol toSymbol(abool()) = \bool();
Symbol toSymbol(areal()) = \real();
Symbol toSymbol(arat()) = \rat();
Symbol toSymbol(astr()) = \str();
Symbol toSymbol(anum()) = \num();
Symbol toSymbol(anode()) = \node();
Symbol toSymbol(avoid()) = \void();
Symbol toSymbol(avalue()) = \value();
Symbol toSymbol(aloc()) = \loc();
Symbol toSymbol(adatetime()) = \datetime();
Symbol toSymbol(alist(AType elmType)) = \list(toSymbol(elmType));
Symbol toSymbol(aset(AType elmType)) = \set(toSymbol(elmType));
Symbol toSymbol(atuple(atypeList(list[AType] elmTypes))) = \tuple([toSymbol(elmType) | elmType <- elmTypes]);
Symbol toSymbol(amap(Atype t1, AType t2)) = \map(toSymbol(t1), toSymbol(t2));
Symbol toSymbol(arel(atypeList(list[AType] elmTypes))) = \rel([toSymbol(elmType) | elmType <- elmTypes]);
Symbol toSymbol(alrel(atypeList(list[AType] elmTypes))) = \lrel([toSymbol(elmType) | elmType <- elmTypes]);
Symbol toSymbol(aadt(str adtName)) = \adt(adtName, []);
Symbol toSymbol(tvar(name)) {
    throw TypeUnavailable();
}
default Symbol toSymbol(AType t) {
    throw "toSymbol cannot convert <t>";
}

AType toAType(\int()) = aint();
AType toAType(\bool()) = abool();
AType toAType(\real()) = areal();
AType toAType(\rat()) = arat();
AType toAType(\str()) = astr();
AType toAType(\num()) = anum();
AType toAType(\node()) = anode();
AType toAType(\void()) = avoid();
AType toAType(\value()) = avalue();
AType toAType(\loc()) = aloc();
AType toAType(\datetime()) = adatetime();
AType toAType(\list(Symbol elmType)) = alist(toAType(elmType));
AType toAType(\set(Symbol elmType)) = aset(toAType(elmType));
AType toAType(\tuple(list[Symbol] elmTypes)) = atuple(atypeList([toAType(elmType) | elmType <- elmTypes]));
AType toAType(\map(Symbol from, Symbol to)) = amap(toAType(from), toAType(to));
AType toAType(\rel(list[Symbol] elmTypes)) = arel(atypeList([toAType(elmType) | elmType <- elmTypes]));
AType toAType(\lrel(list[Symbol] elmTypes)) = alrel(atypeList([toAType(elmType) | elmType <- elmTypes]));
AType toAType(\adt(str adtName, list[Symbol] parameters)) = aadt(adtName);

//str AType2String(tvar(name)) = "<name>";
//str AType2String(lub(list[AType] atypes)) = "lub([<intercalate(",", [AType2String(t) | t <- atypes])>])";
str AType2String(acons(str adtName, str consName, 
                 lrel[AType fieldType, str fieldName] fields, 
                 lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields))
                 = "<adtName>:<consName>(<intercalate(",", ["<AType2String(ft)> <fn>" | <ft, fn> <- fields])>,<kwFields>)";

str AType2String(afunc(AType ret, list[AType] formals, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals))
                = "<AType2String(ret)>(<intercalate(",", [AType2String(f) | f <- formals])>,<kwFormals>)";
                
str AType2String(AType t) = prettyPrintType(toSymbol(t));

data IdRole
    = moduleId()
    | functionId()
    | variableId()
    | formalId()
    | labelId()
    | constructorId()
    ;

set[IdRole] possibleOverloads = {functionId(), constructorId()};

data PathLabel
    = importLabel()
    | extendLabel()
    ;

data Vis
    = publicVis()
    | privateVis()
    ;

data Modifier
    = javaModifier()
    | testModifier()
    | defaultModifier()
    ;

// Add visibility information to definitions
data DefInfo(Vis vis = publicVis());

// Maintain conditionalScopes: map to subrange where definitions are valid
map[Key,Key] elseScopes = ();

void addElseScope(Tree cond, Tree elsePart){
    elseScopes[getLoc(cond)] = getLoc(elsePart);
}

bool isSubType(AType t1, AType t2) = subtype(toSymbol(t1), toSymbol(t2));
AType getLUB(AType t1, AType t2) = toAType(lub(toSymbol(t1), toSymbol(t2)));

AType getVoid() = avoid();
AType getValue() = avalue();

set[AType] numericTypes = { aint(), areal(), arat(), anum() };

// Name resolution filters

Accept isAcceptableSimple(FRModel frm, Key def, Use use){
    
    //println("isAcceptableSimple: id=<use.id> def=<def>, use=<use>");
    res = acceptBinding();

    if(variableId() in use.idRoles){
       // enforce definition before use
       if(def < use.scope && use.occ.offset < def.offset){
           res = ignoreContinue();
           //println("isAcceptableSimple =\> <res>");
           return res;
       }
       // restrict when in conditional scope
       if(elseScopes[use.scope]?){
          if(use.occ < elseScopes[use.scope]){
             res = ignoreContinue();
             //println("isAcceptableSimple =\> <res>");
             return res;
          }
       }
    }
    //println("isAcceptableSimple =\> <res>");
    return res;
}

// Rascal-specific defines

Tree define(FunctionDeclaration decl, Tree scope, FRBuilder frb){
    signature = decl.signature;
    body = decl.body;
    name = signature.name;
    retType = toAType(convertType(signature.\type));
    parameters = signature.parameters;
    formals = [pat | Pattern pat <- parameters.formals.formals];
   
    kwFormals = getKeywordFormals(parameters.keywordFormals);
    frb.define(scope, "<name>", functionId(), name, defType(formals, AType() { return afunc(retType, [typeof(f) | f <- formals], kwFormals); }));
    return decl;
}

lrel[AType, str, Expression] getKeywordFormals(KeywordFormals kwFormals){
    if(kwFormals is none) return [];
    
    return 
        for(KeywordFormal kwf <- kwFormals.keywordFormalList){
            fieldType = toAType(convertType(kwf.\type));
            fieldName = "<kwf.name>";
            defaultExp = kwf.expression;
            append <fieldType, fieldName, defaultExp>;
        }
}

Tree define ((Declaration) `<Tags tags> <Visibility visibility> data <UserType user> <CommonKeywordParameters commonKeywordParameters> = <{Variant "|"}+ variants> ;`, Tree scope, FRBuilder frb){
    adtName = "<user.name>";
    for(Variant v <- variants){
        consName = "<v.name>";
        fields = 
            for(TypeArg ta <- v.arguments){
                fieldType = toAType(convertType(ta.\type));
                fieldName = ta has name ? "<ta.name>" : "";
                append <fieldType, fieldName>;
            }
    
       kwFields = [];
       if(v.keywordArguments is \default){
        kwFields =
            for(KeywordFormal kwf <- v.keywordArguments.keywordFormalList){
                fieldType = toAType(convertType(kwf.\type));
                fieldName = "<kwf.name>";
                defaultExp = kwf.expression;
                append <fieldType, fieldName, defaultExp>;
            }
        }
        consType = acons(adtName, consName, fields, kwFields);
        frb.define(scope, consName, constructorId(), v.name, defType(consType));
    }
    return scope;
}


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
               return getLUB(t1, t2);
            }
            switch([t1, t2]){
                case [alist(e1), x]: return alist(e2) := x ? alist(getLUB(e1, e2)) : alist(getLUB(e1, x));
                case [aset(e1), x]: return aset(e2) := x ? aset(getLUB(e1, e2)) : aset(getLUB(e1, x));
                //case [\map(e1a, e2a), \map(e1b, e2b)]: return rascalType(\map(lub(e1a,e1b), lub(e2a,e2b)));
                //case [\tuple(e1), \tuple(e2)]: return rascalType(\tuple(lub(e1, e2)));
                case [astr(), astr()]: return astr();
                case [aloc(), astr()]: return aloc();       
            }
            if(alist(e2) := t2){
                return alist(getLUB(t1, e2));
            }
            if(aset(e2) := t2){
                return aset(getLUB(t1, e2));
            }
                
             reportError(exp, "No version of `+` is applicable for % and %", exp1, exp2);    
      }); 
}

Tree define(exp: (Expression) `<Expression exp1> || <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, abool());
      
    frb.require("`||` operator", exp, [exp1, exp2],
        (){ if(abool() != typeof(exp1)) reportError(exp1, "Argument of || should be `bool`, found %", exp1);
            if(abool() != typeof(exp2)) reportError(exp2, "Argument of || should be `bool`, found %", exp2);
            // TODO: check that exp1 and exp2 introduce the same set of variables
          });
    return scope;
}

Tree define(exp: (Expression) `<Expression exp1> && <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, abool());
   
    frb.require("`&&` operator", exp, [exp1, exp2],
        (){ if(abool() != typeof(exp1)) reportError(exp1, "Argument of && should be `bool`, found %", exp1);
            if(abool() != typeof(exp2)) reportError(exp2, "Argument of && should be `bool`, found %", exp2);
          });
    return scope;
}

void collect(exp: (Expression) `<Expression exp1> == <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, abool());
    frb.require("`==` operator", exp, [exp1, exp2],
        (){ comparable(typeof(exp1), typeof(exp2), onError(exp, "`==` operator not defined for % and %", exp1, exp2));
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
                    comparable(ptype, etype, onError(exp, "Cannot match % pattern with % subject", pat, expression));
                 } else {
                    unify(ptype, etype, onError(pat, "Type of pattern could not be computed"));
                 }
                 fact(pat, typeof(pat));
               });
    }
}

void checkKwArgs(lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals, keywordArguments){
    if(keywordArguments is none) return;
 
    next_arg:
    for(kwa <- keywordArguments.keywordArgumentList){ 
        kwName = "<kwa.name>";
        kwType = typeof(kwa.expression);
        for(<ft, fn, de> <- kwFormals){
           if(kwName == fn){
              if(!comparable(kwType, ft)){
                reportError(kwa, "Keyword argument % has type %, expected %", kwName, kwType, ft);
              }
              continue next_arg;
           } 
        }
        reportError(kwa, "Undefined keyword argument %", kwName);
    }
 }                   

void collect(callOrTree: (Expression) `<Expression expression> ( <{Expression ","}* arguments> <KeywordArguments[Expression] keywordArguments>)`, Tree scope, FRBuilder frb){
    actuals = [a | Expression a <- arguments];
    
    frb.calculate("call", callOrTree, actuals,
        AType(){        
                if(overloadedType(rel[Key, AType] overloads) := typeof(expression)){
                  next_fun:
                    for(<key, tp> <- overloads){                       
                        if(afunc(AType ret, list[AType] formals, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals) := tp){
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
                        if(acons(str adtName, str consName, lrel[AType fieldType, str fieldName] fields, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields) := tp){
                            nactuals = size(actuals); nformals = size(fields);
                            if(nactuals != nformals) continue next_cons;
                            for(int i <- index(actuals)){
                                if(!comparable(typeof(actuals[i]), fields[i].fieldType)) continue next_cons;
                            }
                            checkKwArgs(kwFields, keywordArguments);
                            return aadt(adtName);
                        }
                    }
                    reportError(callOrTree, "No function or constructor `<expression>` for arguments %", [actuals]);
                }
                if(afunc(AType ret, list[AType] formals, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals) := typeof(expression)){
                    nactuals = size(actuals); nformals = size(formals);
                    if(nactuals != nformals){
                        reportError(callOrTree, "Expected <nformals> argument<nformals != 1 ? "s" : ""> for `<expression>`, found <nactuals>");
                    }
                    for(int i <- index(actuals)){
                        comparable(typeof(actuals[i]), formals[i], onError(actuals[i], "Argument of `<expression>` should have type %, found %", formals[i], actuals[i]));
                    }
                    checkKwArgs(kwFormals, keywordArguments);
                    return ret;
                }
                if(acons(str adtName, str consName, lrel[AType fieldType, str fieldName] fields, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields) := typeof(expression)){
                    nactuals = size(actuals); nformals = size(fields);
                    if(nactuals != nformals){
                        reportError(callOrTree, "Expected <nformals> argument<nformals != 1 ? "s" : ""> for `<expression>`, found <nactuals>");
                    }
                    for(int i <- index(actuals)){
                        comparable(typeof(actuals[i]), fields[i].fieldType, onError(actuals[i], "Field should have type %, found % ", fields[i].fieldType, actuals[i]));
                    }
                    return aadt(adtName);
                }
                reportError(callOrTree, "Function or constructor type required for `<expression>`, found %", [expression]);
        });
}



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
    declaredType = toAType(convertType(tp));
    frb.atomicFact(pat, declaredType);
    frb.define(scope, "<name>", variableId(), name, defType(declaredType));
    return scope;
}

void collect(listPat: (Pattern) `[ <{Pattern ","}* elements0> ]`, Tree scope, FRBuilder frb){
    pats = [ p | Pattern p <- elements0 ];
   
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
   
    for(pat <- pats){
        if(namePat: (Pattern) `<QualifiedName name>` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return typeof(tau); }));
        }
        if(splicePat: (Pattern) `*<QualifiedName name>` := pat || splicePat: (Pattern) `<QualifiedName name>*` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return aset(typeof(tau)); }));
        }
        if(splicePlusPat: (Pattern) `+<QualifiedName name>` := pat){
            tau = frb.newTypeVar(scope);
            frb.atomicFact(pat, tau);
            frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return aset(typeof(tau)); }));
        }
    }
    
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

// A few statements

void collect(stat: (Statement) `<Expression expression>;`,  Tree scope, FRBuilder frb){
    frb.fact(stat, [expression], AType(){ return typeof(expression); });
}

Tree define(stat: (Statement) `<QualifiedName name> = <Statement statement>`, Tree scope, FRBuilder frb){
    frb.fact(stat, [statement], AType(){ return typeof(statement); });
    frb.define(scope, "<name>", variableId(), name, defLub([statement], AType(){ return typeof(statement); }));
    frb.require("assignment to variable `<name>`", stat, [name, statement],
                () { subtype(typeof(statement), typeof(name), onError(stat, "Incompatible type in assignment to variable `<name>`", statement)); });  
    
    return scope;
}

Tree define(stat: (Statement) `<Type tp> <{Variable ","}+ variables>;`, Tree scope, FRBuilder frb){
    println(convertType(tp));
    declaredType = toAType((convertType(tp)));
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
    
    frb.require("if then", stat, condList + [thenPart],
        (){
            for(cond <- condList){
                if(abool() != typeof(cond)) reportError(cond, "Condition should be `bool`, found %", cond);
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
    
    frb.require("if then else", stat, condList + [thenPart, elsePart],
        (){
            for(cond <- condList){
                if(abool() != typeof(cond)) reportError(cond, "Condition should be `bool`, found %", cond);
            }  
            fact(stat, getLUB(typeof(thenPart), typeof(elsePart)));
        });
    return conditions; // thenPart may refer to variables defined in conditions; elsePart may not
}


// ----  Examples & Tests --------------------------------

private start[Expression] sampleExpression(str name) = parse(#start[Expression], |home:///git/TypePal/src/rascal/<name>.rsc-exp|);
private start[Module] sampleModule(str name) = parse(#start[Module], |home:///git/TypePal/src/rascal/<name>.rsc|);

set[Message] validateModule(str name) {
    startTime = cpuTime();
    b = sampleModule(name).top;
    afterParseTime = cpuTime();
    m = extractFRModel(b, newFRBuilder(debug=false));
    afterExtractTime = cpuTime();
    msgs = validate(m, isSubType=isSubType, getLUB=getLUB, getATypeMin=getVoid, getATypeMax=getValue, mayBeOverloaded=possibleOverloads, debug=true).messages;
    afterValidateTime = cpuTime();
    //println("parse:    <(afterParseTime - startTime)/1000000> ms
    //        'extract:  <(afterExtractTime - afterParseTime)/1000000> ms
    //        'validate: <(afterValidateTime - afterExtractTime)/1000000> ms
    //        'total:    <(afterValidateTime - startTime)/1000000> ms");
    return msgs;
}

set[Message] validateExpression(str name) {
    b = sampleExpression(name);
    m = extractFRModel(b, newFRBuilder(),debug=true);
    return validate(m, isSubType=isSubType, getLUB=getLUB, getATypeMin=getVoid, getATypeMax=getValue, debug=false).messages;
}


void testExp() {
    runTests(|project://TypePal/src/rascal/exp.ttl|, #Expression, isSubType=isSubType, getLUB=getLUB, getATypeMin=getVoid, getATypeMax=getValue, mayBeOverloaded=possibleOverloads);
}

void testPat() {
    runTests(|project://TypePal/src/rascal/pat.ttl|, #Expression, isSubType=isSubType, getLUB=getLUB, getATypeMin=getVoid, getATypeMax=getValue, mayBeOverloaded=possibleOverloads);
}

void testModule() {
    runTests(|project://TypePal/src/rascal/fundecl.ttl|, #Module, isSubType=isSubType, getLUB=getLUB, getATypeMin=getVoid, getATypeMax=getValue, mayBeOverloaded=possibleOverloads);
}
