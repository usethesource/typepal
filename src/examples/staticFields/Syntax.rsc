module examples::staticFields::Syntax

// ---- Programs with struct declarations and uses ----------------------------

extend examples::CommonLex;

start syntax Program = Declaration*;

syntax Type = "int" | "str" | Id typ;

syntax Declaration
    = Type typ Id id "=" Expression exp ";"
    | "struct" Id name "{" {Field ","}* fields "}" ";"
    ;
    
syntax Field = Type typ Id name ;

syntax Expression 
    = Integer i
    | String s
    | Id use
    | Expression lhs "." Id fieldName
    | "new" Id name
    ;
    
keyword Keywords = "int" | "str" | "struct" | "new";