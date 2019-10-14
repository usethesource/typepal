module examples::smallOO::Syntax

// ---- SmallOO syntax --------------------------------------------------------

extend lang::std::Layout;

start syntax Module = "module" Identifier moduleName Import* imports Declaration* declarations; 

syntax Import = "import" Identifier moduleName;

syntax Declaration 
    = "class" Identifier className "{" Declaration* declarations "}"
    | Type returnType Identifier functionName "(" {Parameter ","}* parameters ")" "=" Expression returnExpression ";"
    | Type fieldType Identifier fieldName ";"
    ;

syntax Parameter = Type tp Identifier name; 

syntax Expression
    = Identifier id
    | Expression "." Identifier id
    | Literal l
    | Identifier functionName "(" {Expression ","}* parameters ")"
    | Expression "." Identifier functionName "(" {Expression ","}* parameters ")"
    | Expression "+" Expression
    ;
    
lexical Identifier = ([a-z A-Z _][a-z A-Z _ 0-9]* !>> [a-z A-Z _ 0-9]) \ Keywords;
    
lexical Literal
    = Integer
    | String
    ;
    
lexical Integer = [0-9]+ !>> [0-9];
lexical String = [\"] ![\"]* [\"];
    
lexical Type
    = "int"
    | "str"
    | Identifier className
    ;

keyword Keywords = "module" | "class" | "import" | "int" | "str";