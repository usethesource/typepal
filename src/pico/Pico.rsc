module pico::Pico

// Pico, a trivial language, single scope, no functions

import Prelude;
extend Constraints;

// ----  Pico syntax -------------------------------------

lexical Id  = [a-z][a-z0-9]* !>> [a-z0-9];
lexical Natural = [0-9]+ ;
lexical String = "\"" ![\"]*  "\"";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
   | @category="Comment" ws3: "%%" ![\n]* $
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

str AType2String(intType()) = "`int`";
str AType2String(strType()) = "`str`";

// ----  Def/Use -----------------------------------------
 
Tree define(d:(Declaration) `<Id id> : <Type tp>`,  Tree scope, SGBuilder sgb) {
     sgb.define(scope, "<d.id>", variableId(), d, defInfo(transType(tp)));
     return scope; 
}

void use(e: (Expression) `<Id name>`, Tree scope, SGBuilder sgb){
     sgb.use(scope, name, {variableId()}, 0);
}

void use((Statement) `<Id var> := <Expression val>`, Tree scope, SGBuilder sgb){
     sgb.use(scope, var, {variableId()}, 0);
}

// ----  Requirements ------------------------------------

void require(s: (Statement) `<Id var> :=  <Expression val>`, SGBuilder sgb){
     sgb.require("assignment", s, 
                 [ equal(typeof(var), typeof(val), onError(s, "Lhs <var> should have same type as rhs")) ]);
}

void require(s: (Statement) `if <Expression cond> then <{Statement ";"}*  thenPart> else <{Statement ";"}* elsePart> fi` , SGBuilder sgb){
     sgb.require("int_condition", s, 
                 [ equal(typeof(s.cond), intType(), onError(s.cond, "Condition")) ]);
}

void require(s: (Statement) `while <Expression cond> do <{Statement ";"}* body> od` , SGBuilder sgb){
     sgb.require("int_condition", s, 
                 [ equal(typeof(s.cond), intType(), onError(s.cond, "Condition")) ]);
}

void require(e: (Expression) `<Expression lhs> + <Expression rhs>`, SGBuilder sgb){
     sgb.overload("addition", e, 
                  [lhs, rhs], [<[intType(), intType()], intType()>, <[strType(), strType()], strType()>],
                  onError(e, "No version of + exists for given argument types"));
}

void require(e: (Expression) `<Expression lhs> - <Expression rhs>`, SGBuilder sgb){
     sgb.require("subtraction", e, 
                 [ equal(typeof(lhs), intType(), onError(lhs, "Lhs of -")),
                   equal(typeof(rhs), intType(), onError(rhs, "Rhs of -")),
                   fact(e, intType())
                 ]);
}

void require(e: (Expression) `<String string>`, SGBuilder sgb){
    sgb.fact(e, strType());
}

void require(e: (Expression) `<Natural natcon>`, SGBuilder sgb){
    sgb.fact(e, intType());
}

// ----  Examples & Tests --------------------------------

public Program samplePico(str name) = parse(#Program, |project://TypePal/src/pico/<name>.pico|);

set[Message] validatePico(str name) = validate(extractScopesAndConstraints(samplePico(name)));
