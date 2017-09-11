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
     = rascalType(Symbol symbol)
     ;
data IdRole
    = moduleId()
    | functionId()
    | variableId()
    | formalId()
    | labelId()
    ;

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

str AType2String(rascalType(Symbol s)) = prettyPrintType(s);

bool isSubType(rascalType(Symbol s1), rascalType(Symbol s2)) = subtype(s1, s2);
AType getLUB(rascalType(t1), rascalType(t2)) = rascalType(lub(t1, t2));

set[Symbol] numericTypes = { Symbol::\int(), Symbol::\real(), Symbol::\rat(), Symbol::\num() };

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

Tree declare(FunctionDeclaration fd, Tree scope, FRBuilder frb){
    println("<fd>");
    return scope;

}

// Check the types of Rascal literals
void collect(Literal l:(Literal)`<IntegerLiteral il>`, Tree scope, FRBuilder frb){
    frb.atomicFact(il, rascalType(Symbol::\int()));
}

void collect(Literal l:(Literal)`<RealLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, rascalType(Symbol::\real()));
}

void collect(Literal l:(Literal)`<BooleanLiteral bl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, rascalType(Symbol::\bool()));
 }

void collect(Literal l:(Literal)`<DateTimeLiteral dtl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, rascalType(Symbol::\datetime()));
}

void collect(Literal l:(Literal)`<RationalLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, rascalType(Symbol::\rat()));
}

//void collect(Literal l:(Literal)`<RegExpLiteral rl>`, Configuration c) {

void collect(Literal l:(Literal)`<StringLiteral sl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, rascalType(Symbol::\str()));
}

void collect(Literal l:(Literal)`<LocationLiteral ll>`, Tree scope, FRBuilder frb){
    frb.atomicFact(l, rascalType(Symbol::\loc()));
}

// A few expressions

void collect(exp: (Expression) `<QualifiedName name>`, Tree scope, FRBuilder frb){
    frb.use(scope, name, {variableId(), formalId()});
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
            if(rascalType(t1) := typeof(exp1) && rascalType(t2) := typeof(exp2)){
                if(t1 in numericTypes && t2 in numericTypes){
                   return rascalType(lub(t1, t2));
                }
                switch([t1, t2]){
                    case [\list(e1), x]: return \list(e2) := x ? rascalType(\list(lub(e1, e2))) : rascalType(\list(lub(e1, x)));
                    case [\set(e1), x]: return \set(e2) := x ? rascalType(\set(lub(e1, e2))) : rascalType(\set(lub(e1, x)));
                    case [\map(e1a, e2a), \map(e1b, e2b)]: return rascalType(\map(lub(e1a,e1b), lub(e2a,e2b)));
                    case [\tuple(e1), \tuple(e2)]: return rascalType(\tuple(lub(e1, e2)));
                    case [\str(), \str()]: return rascalType(\str());
                    case [\loc(), \str()]: return rascalType(Symbol::\loc());       
                }
                if(\list(e2) := t2){
                    return rascalType(\list(lub(t1, e2)));
                }
                if(\set(e2) := t2){
                    return rascalType(\set(lub(t1, e2)));
                }
             }   
             reportError(exp, "No version of `+` is applicable", [exp1, exp2]);    
      }); 
}

Tree define(exp: (Expression) `<Expression exp1> || <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, rascalType(\bool()));
      
    frb.require("`||` operator", exp, [exp1, exp2],
        (){ if(rascalType(\bool()) != typeof(exp1)) reportError(exp1, "Argument of || should be `bool`", [exp1]);
            if(rascalType(\bool()) != typeof(exp2)) reportError(exp2, "Argument of || should be `bool`", [exp2]);
            // TODO: check that exp1 and exp2 introduce the same set of variables
          });
    return scope;
}

Tree define(exp: (Expression) `<Expression exp1> && <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, rascalType(\bool()));
   
    frb.require("`&&` operator", exp, [exp1, exp2],
        (){ if(rascalType(\bool()) != typeof(exp1)) reportError(exp1, "Argument of && should be `bool`", [exp1]);
            if(rascalType(\bool()) != typeof(exp2)) reportError(exp2, "Argument of && should be `bool`", [exp2]);
          });
    return scope;
}

void collect(exp: (Expression) `<Expression exp1> == <Expression exp2>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, rascalType(\bool()));
    frb.require("`==` operator", exp, [exp1, exp2],
        (){ comparable(typeof(exp1), typeof(exp2), onError(exp, "`==` operator"));
          });
}

void collect(exp: (Expression) `[ <{Expression ","}* elements0> ]`, Tree scope, FRBuilder frb){
    elms = [ e | Expression e <- elements0 ];
    if(isEmpty(elms)){
        frb.atomicFact(exp, rascalType(\list(Symbol::\void())));    // TODO: some trigger missing: we cannot use the calculate only
    } else {
        frb.calculate("list expression", exp, elms,
            AType() {
                return rascalType(\list((Symbol::\void() | lub(it, t) | elm <- elms, rascalType(t) := typeof(elm))));
            });
        }
}

void collect(exp: (Expression) `{ <{Expression ","}* elements0> }`, Tree scope, FRBuilder frb){
    elms = [ e | Expression e <- elements0 ];
    if(isEmpty(elms)){
        frb.atomicFact(exp, rascalType(\set(Symbol::\void())));
    } else {
        frb.calculate("set expression", exp, elms,
            AType() {
                return rascalType(\set((Symbol::\void() | lub(it, t) | elm <- elms, rascalType(t) := typeof(elm))));
            });
    }
}

void collect(exp: (Expression) `\< <{Expression ","}* elements1> \>`, Tree scope, FRBuilder frb){
    elms = [ e | Expression e <- elements1 ];
    frb.calculate("tuple expression", exp, elms,
        AType() {
                return rascalType(\tuple([ t | elm <- elms, rascalType(t) := typeof(elm) ]));
        });
}

void collect(exp: (Expression) `<Pattern pat> := <Expression expression>`, Tree scope, FRBuilder frb){
    frb.atomicFact(exp, rascalType(\bool()));
    if(pat is  qualifiedName){
        name = pat.qualifiedName;
        frb.define(scope, "<name>", variableId(), name, defLub([expression], AType(){ return typeof(expression); }));
        frb.require("match variable `<name>`", exp, [name, expression],
                () { comparable(typeof(expression), typeof(name), onError(exp, "Incompatible type in match using `<name>`")); });  
    } else {
        frb.require("`:=` operator", exp, [expression],
            () { println("typeof(pat): <typeof(pat)>; typeof(expression): <typeof(expression)>");
                 if(rascalType(ptype) := typeof(pat) && rascalType(psubj) := typeof(expression) && !comparable(ptype, psubj)){
                    unify(typeof(pat), typeof(expression), onError(exp, "Match operator `:=`"));
                 }
                 //comparable(typeof(pat), typeof(expression), onError(exp, "Match operator `:=`"));
                 fact(pat, typeof(pat));
               });
    }
}

// A few patterns

void collect(Pattern pat:(Literal)`<IntegerLiteral il>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, rascalType(Symbol::\int()));
}

void collect(Pattern pat:(Literal)`<RealLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, rascalType(Symbol::\real()));
}

void collect(Pattern pat:(Literal)`<BooleanLiteral bl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, rascalType(Symbol::\bool()));
 }

void collect(Pattern pat:(Literal)`<DateTimeLiteral dtl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, rascalType(Symbol::\datetime()));
}

void collect(Pattern pat:(Literal)`<RationalLiteral rl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, rascalType(Symbol::\rat()));
}

//void collect(Literalpat:(Literal)`<RegExpLiteral rl>`, Configuration c) {

void collect(Pattern pat:(Literal)`<StringLiteral sl>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, rascalType(Symbol::\str()));
}

void collect(Pattern pat:(Literal)`<LocationLiteral ll>`, Tree scope, FRBuilder frb){
    frb.atomicFact(pat, rascalType(Symbol::\loc()));
}
            
void collect(Pattern pat: (Pattern) `<QualifiedName name>`, Tree scope, FRBuilder frb){
    tau = frb.newTypeVar(scope);
    frb.define(scope, "<name>", variableId(), name, defLub([], AType() { return typeof(tau); }));
}

Tree define(Pattern pat: (Pattern) `<Type tp> <Name name>`, Tree scope, FRBuilder frb){
    declaredType = rascalType(convertType(tp));
    frb.atomicFact(pat, declaredType);
    frb.define(scope, "<name>", variableId(), name, defType(declaredType));
    return scope;
}

void collect(pat: (Pattern) `[ <{Pattern ","}* elements0> ]`, Tree scope, FRBuilder frb){
    elms = [ p | Pattern p <- elements0 ];
    if(isEmpty(elms)){
        frb.atomicFact(pat, rascalType(\list(Symbol::\void())));    // TODO: some trigger missing: we cannot use the calculate only
    } else {
        for(int i <- index(elms)){
            frb.atomicFact(elms[i], frb.newTypeVar(scope));
        }
        frb.calculate("list pattern", pat, elms, AType() { 
                lubbedType = (Symbol::\void() | lub(it, t) | elm <- elms, rascalType(t) := typeof(elm));
                elmType = (rascalType(lubbedType) | lub(it, t) | elm <- elms, rascalType(t) !:= typeof(elm));
                res = 
                println("list pattern: <res>");
                return res;
            });
    }
}

void collect(pat: (Pattern) `{ <{Pattern ","}* elements0> }`, Tree scope, FRBuilder frb){
    elms = [ p | Pattern p <- elements0 ];
    if(isEmpty(elms)){
        frb.atomicFact(pat, rascalType(\set(Symbol::\void())));    // TODO: some trigger missing: we cannot use the calculate only
    } else {
        frb.calculate("set pattern", pat, elms,
            AType() {
                return rascalType(\set((Symbol::\void() | lub(it, t) | elm <- elms, rascalType(t) := typeof(elm))));
            });
        }
}

void collect(pat: (Pattern) `\< <{Pattern ","}+ elements1> \>`, Tree scope, FRBuilder frb){
    elms = [ p | Pattern p <- elements1 ];
    frb.calculate("tuple pattern", pat, elms,
        AType() {
                return rascalType(\tuple([ t | elm <- elms, rascalType(t) := typeof(elm) ]));
        });
}

// A few statements

void collect(stat: (Statement) `<Expression expression>;`,  Tree scope, FRBuilder frb){
    frb.fact(stat, [expression], AType(){ return typeof(expression); });
}

Tree define(stat: (Statement) `<QualifiedName name> = <Statement statement>`, Tree scope, FRBuilder frb){
    frb.fact(stat, [statement], AType(){ return typeof(statement); });
    frb.define(scope, "<name>", variableId(), name, defLub([statement], AType(){ return typeof(statement); }));
    frb.require("assignment to variable `<name>`", stat, [name, statement],
                () { subtype(typeof(statement), typeof(name), onError(stat, "Incompatible type in assignment to variable `<name>`")); });  
    
    return scope;
}

Tree define(stat: (Statement) `<Type tp> <{Variable ","}+ variables>;`, Tree scope, FRBuilder frb){
    declaredType = rascalType(convertType(tp));
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
    frb.atomicFact(stat, rascalType(\value()));
    
    frb.require("if then", stat, condList + [thenPart],
        (){
            for(cond <- condList){
                if(rascalType(\bool()) != typeof(cond)) reportError(cond, "Condition should be `bool`", [cond]);
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
                if(rascalType(\bool()) != typeof(cond)) reportError(cond, "Condition should be `bool`", [cond]);
            }  
            fact(stat, lub(typeof(thenPart), typeof(elsePart)));
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
    msgs = validate(m, isSubType=isSubType, getLUB=getLUB, debug=true).messages;
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
    return validate(m, isSubType=isSubType, getLUB=getLUB,debug=true).messages;
}


void testExp() {
    runTests(|project://TypePal/src/rascal/exp.ttl|, #Expression, isSubType=isSubType, getLUB=getLUB);
}

void testPat() {
    runTests(|project://TypePal/src/rascal/pat.ttl|, #Expression, isSubType=isSubType, getLUB=getLUB);
}
