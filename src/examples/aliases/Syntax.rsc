module examples::aliases::Syntax

extend examples::CommonLex;

// ---- Programs with struct declarations and aliases -------------------------

start syntax Program = Declaration*;

syntax Type = "int" | "str" | Id typ;

syntax Declaration
    = Type typ Id id "=" Expression exp ";"
    | "struct" Id name "{" {Field ","}* fields "}" ";"
    | "alias" Id name "=" Type typ ";"
    ;
    
syntax Field = Type typ Id name ;

syntax Expression 
    = Integer i
    | String s
    | Id use
    | Expression lhs "." Id fieldName
    | "new" Id name
    ;
    
keyword Keywords = "alias" | "int" | "str" | "struct" | "new";