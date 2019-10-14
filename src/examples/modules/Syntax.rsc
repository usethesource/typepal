module examples::modules::Syntax

extend lang::std::Layout;

keyword Reserved =  "struct" | "int" | "import";

start syntax Program =
	"module" ModuleId
	Import* imports
	TopLevelDecl* declarations;
	

	
lexical ModuleId
    = {Id "::"}+ moduleName
    ;

lexical Id 
	=  (([a-z A-Z 0-9 _] - [u s]) !<< ([a-z A-Z] - [u s])[a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Reserved 
	;


syntax Import
	= "import" ModuleId
 	;
	
syntax TopLevelDecl
	=  "struct" Id  "{" DeclInStruct* declarations "}"
	;
	
syntax DeclInStruct
	= Type ty 
	;

syntax Type
	= Id id 
	;

