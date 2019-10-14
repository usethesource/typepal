module examples::extending::Syntax

extend examples::CommonLex;

// ---- Programs with struct declarations and aliases -------------------------

start syntax Program = StructModule* ExecModule*;

syntax StructModule
    = "struct" Id name "{" Import* imports VarDecl* fields "}"
    ;
    
syntax ExecModule
    = "exec" Id name "{" Import* imports Extend* extends VarDecl* fields "}"
    ;

syntax Import = "import" Id id ;
syntax Extend = "extend" Id id ;

syntax Type = "int" | Id userDefinedType;


syntax VarDecl = "var" Id fieldId ":" Type ty "=" Expr e;
    
syntax Expr  
    = 
    "new" Id structId
    | "0"
    | Ref r
    | Expr expression "." Id field
    ;  
    
syntax Ref
	 = ( Id moduleId "::")? qualification Id varId;

keyword Keywords = "struct" | "exec" | "import" | "extend" | "var" | "new" | "int" ;