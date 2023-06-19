module examples::dataModel::Syntax

extend examples::CommonLex;

// Syntax 
start syntax Program = Declaration+ decls;

syntax Declaration
    = "entity" Id name  "{" Field+ fields "}"
    ;

syntax Type = "int" | "str" | Id typ | "Set" "\<" Type elmType  "\>";

keyword Keywords 
    = "int"
    | "str"
    | "Set"
    | "entity"
    | "field"
    | "inverse"
    ;
   
syntax Field 
    =  biReference: Id name "-\>" Type typ "inverse" Id ref "::" Id attr
    ;