module examples::structParameters::Syntax

// ---- Programs with struct declarations and uses ----------------------------

extend examples::CommonLex;

start syntax Program = Declaration*;

syntax Type = "int" | "str" | Id TypeActuals;
    
syntax TypeActuals
    = noActuals: ()
    | withTypeActuals: "[" {Type ","}+ actuals "]"
    ;
    
syntax TypeHeader
    = Id TypeFormals
    ;

syntax TypeFormals
    = noTypeFormals: ()
    | withTypeFormals: "[" {TypeFormal ","}+ formals"]"
    ;
    
syntax TypeFormal
    = Id
    ;
    
syntax Declaration
    = Type typ Id id "=" Expression exp ";"
    | "struct" TypeHeader "{" {Field ","}* fields "}" ";"
    ;
    
syntax Field = Type typ Id name ;

syntax Expression 
    = Integer i
    | String s
    | Id use
    | Expression lhs "." Id fieldName
    | "new" Id name TypeActuals
    ;
    
keyword Keywords = "int" | "str" | "struct" | "new";