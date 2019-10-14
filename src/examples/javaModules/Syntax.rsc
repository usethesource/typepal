module lang::javaModules::Syntax

extend lang::std::Whitespace;
extend lang::std::Comment;

// Java with Modules

// ----  syntax ---------------------------------------------------------------

lexical InterfaceId  = ([A-Z][A-Zåa-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Id       = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;

keyword Reserved = "interface" | "extends" | "this" | "return";

//layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical Comment = @category="Comment" "/*" (![*] | [*] !>> [/])* "*/";

layout Layout = (Comment | Whitespace)* !>> [\u0009-\u000D \u0020 \u0085 \u00A0 \u1680 \u180E \u2000-\u200A \u2028 \u2029 \u202F \u205F \u3000] !>> "/*" !>> "//";



lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "%" ![%]+ "%"
   ;
   
start syntax JavaModulesProgram
    = InterfaceDecl* interfacedecls
    ;
    
syntax PackageId
	= {Id "."}+ subPackages;

syntax FQInterfaceId = PackageId path "." InterfaceId;
    
syntax InterfaceDecl
    = "package" PackageId packageId ";" "public interface" InterfaceId  Extends? extends "{" 
              MethodDecl* methoddecls
        "}"
     ;

syntax Extends = "extends" FQInterfaceId ecid ;

syntax Formal
    =  FQInterfaceId cid Id id
    ;
    
syntax Formals
    = "(" {Formal ","}* formals ")"
    ;
          
syntax MethodDecl
    = "default" FQInterfaceId cid Id mid Formals formals "{" "return" Expression exp ";" "}"
    ;
    
syntax Expression
    = Variable var
    | Method method Expressions exps
    | Expression exp "." Method method Expressions exps
    | "0"
    ;

syntax Interface
    = InterfaceId id
    ;
    
syntax Variable
    = Id id
    ;

syntax Method
    = Id id
    ;
           
syntax Expressions
    = "(" {Expression ","}* expressions ")"
    ;   

