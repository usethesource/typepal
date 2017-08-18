module pico::Pico

// Pico, a trivial language, single scope, no functions

import Prelude;

extend typepal::TypePal;

// ----  Pico syntax -------------------------------------

lexical Id  = [a-z][a-z0-9]* !>> [a-z0-9];
lexical Natural = [0-9]+ ;
lexical String = "\"" ![\"]*  "\"";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
//   | @category="Comment" ws3: "{" ![\n}]*  "}"$
   ;
 
start syntax Program 
   = program: "begin" Declarations decls {Statement  ";"}* body "end"
   ;

syntax Declarations 
   = "declare" {Declaration ","}* decls ";" ;  
 
syntax Declaration 
    = decl: Id id ":" Type tp
    ;  
 
syntax Type 
   = natural:"natural" 
   | string :"string"
   ;

syntax Statement 
   = Id var ":=" Expression val                                                                      
   | "if" Expression cond "then" {Statement ";"}*  thenPart "else" {Statement ";"}* elsePart "fi"   
   | "while" Expression cond "do" {Statement ";"}* body "od"                                   
   ;  
     
syntax Expression 
   = Id name                                    
   | String string                          
   | Natural natcon                         
   | bracket "(" Expression e ")"                   
   > left ( Expression lhs "+" Expression rhs                                          
          | Expression lhs "-" Expression rhs  
          )
   ;

// ----  IdRoles, PathLabels and AType ------------------- 

data IdRole
    = variableId()
    ;

data AType = intType() |  strType() ;  

AType transType((Type) `natural`) = intType();
AType transType((Type) `string`) = strType(); 

str AType2String(intType()) = "int";
str AType2String(strType()) = "str";

// ----  Define -----------------------------------------
 
Tree define(d:(Declaration) `<Id id> : <Type tp>`,  Tree scope, FRBuilder frb) {
     frb.define(scope, "<d.id>", variableId(), d, defInfo(transType(tp)));
     return scope; 
}

// ----  Collect uses and requirements ------------------------------------

void collect(e: (Expression) `<Id name>`, Tree scope, FRBuilder frb){
     frb.use(scope, name, {variableId()});;
}

void collect(s: (Statement) `<Id var> := <Expression val>`, Tree scope, FRBuilder frb){
     frb.use(scope, var, {variableId()});
}

// ----  Requirements ------------------------------------

void collect(s: (Statement) `<Id var> :=  <Expression val>`, Tree scope, FRBuilder frb){
     Tree tvar = var; Tree tval = val;
     frb.require("assignment", s, [tvar, tval],
                 (){ equal(typeof(var), typeof(val), onError(s, "Lhs <var> should have same type as rhs")); });
}

void collect(s: (Statement) `if <Expression cond> then <{Statement ";"}*  thenPart> else <{Statement ";"}* elsePart> fi`, Tree scope, FRBuilder frb){
     frb.require("int_condition", s, [s.cond],
         () { equal(typeof(s.cond), intType(), onError(s.cond, "Condition")); });
}

void collect(s: (Statement) `while <Expression cond> do <{Statement ";"}* body> od`, Tree scope, FRBuilder frb){
     frb.require("int_condition", s, [s.cond],
         () { equal(typeof(s.cond), intType(), onError(s.cond, "Condition")); } );
}

void collect(e: (Expression) `<Expression lhs> + <Expression rhs>`, Tree scope, FRBuilder frb){
     frb.overload("addition", e, [lhs, rhs], 
         AType () { switch([typeof(lhs), typeof(rhs)]){
                  case [intType(), intType()]: return intType();
                  case [strType(), strType()]: return strType();
                  default:
                       reportError(e, "Operator `+` cannot be applied", [lhs, rhs]);
               }
            });
}

void collect(e: (Expression) `<Expression lhs> - <Expression rhs>`, Tree scope, FRBuilder frb){
     frb.require("subtraction", e, [lhs, rhs],
         () { equal(typeof(lhs), intType(), onError(lhs, "Lhs of -"));
              equal(typeof(rhs), intType(), onError(rhs, "Rhs of -"));
              fact(e, intType());
            });
}
 
void collect(e: (Expression) `<String string>`, Tree scope, FRBuilder frb){
    frb.atomicFact(e, strType());
}

void collect(e: (Expression) `<Natural natcon>`, Tree scope, FRBuilder frb){
    frb.atomicFact(e, intType());
}

// ----  Examples & Tests --------------------------------

public Program samplePico(str name) = parse(#Program, |home:///git/TypePal/src/pico/<name>.pico|);
                     
set[Message] validatePico(str name) {
    Tree p = samplePico(name);
    ex = extractScopesAndConstraints(p, /*define, collect,*/ makeFRBuilder());
    return validate(ex).messages;
}
 value main() = validatePico("e1");
