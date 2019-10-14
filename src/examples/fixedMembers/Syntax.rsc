module examples::fixedMembers::Syntax

extend examples::CommonLex;

// ---- Programs with struct declarations and aliases -------------------------

start syntax Program = Module*;

syntax Module
    = "module" Id name Import* imports "{" Function* funs Stmt* stmts "}"
    ;

syntax Import = "import" Id id ";";

syntax Function = "fun" Id functionId "{" "}";
    
syntax Stmt = 
    Id moduleId "." Id funId "(" ")" ";"
    ;
   
    
keyword Keywords = "module" | "import" ;