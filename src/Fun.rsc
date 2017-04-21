module Fun

import ParseTree;
extend ScopeGraph;
extend Extract;

// ----  Fun syntax

lexical Id      = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical ModId   = ([A-Z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Integer = [0-9]+ ; 

keyword Reserved = "module" | "import" | "def" | "fun";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
   | @category="Comment" ws3: "%%" ![\n]* $
   ;

syntax Program 
    = ModuleDecl* modules
    ;

syntax ModuleDecl
    = @defscope{module} "module" ModId mid  "{" Decl* decls "}"
    ;
syntax Decl
    = ImportDecl importDecl
    | VarDecl varDecl
    ;
syntax ImportDecl
    = @use{import} "import" ModId mid  "^" Integer defLine ";"
    ;

syntax VarDecl
    = @def{var} "def" Id id "=" Expression expression ";"
    ;
     
syntax Expression 
   = @use{id} a_name: Id name "^" Integer defLine
   | intCon: Integer intcon 
   | @defscope{fun} abstraction: "fun" Id name "{" Expression exp "}"
   | application: Expression exp1 "(" Expression exp2  ")" 
   | left Expression exp1 "*" Expression exp2 
   > left Expression exp1 "+" Expression exp2 
   ;
   
data IdDef
    = moduleIdDef()
    | variableIdDef()
    | parameterIdDef()
    ;
    
data PathLabel
    = importsLabel()
    ;

// Language-specific defines 

void define("module", SGBuilder sg, Key parent, ModuleDecl d)     {
    sg.define(parent, "<d.mid>", moduleIdDef(), d@\loc, noDeclFact()); 
}

void define("var", SGBuilder sg, Key parent, VarDecl d)     {
    sg.define(parent, "<d.id>", variableIdDef(), d@\loc, noDeclFact());  
}

void define("fun", SGBuilder sg, Key parent, Expression exp) {
    sg.define(exp@\loc, "<exp.name>", parameterIdDef(), exp.name@\loc, noDeclFact()); 
}

void use("import", SGBuilder sg, Key parent, ImportDecl d){
    sg.use_ref("<d.mid>", d.mid@\loc, parent, {moduleIdDef()}, importsLabel(), toInt("<d.defLine>"));
}

void use("id", SGBuilder sg, Key parent, Expression exp){
    sg.use("<exp.name>", exp.name@\loc, parent, {variableIdDef(), parameterIdDef()}, toInt("<exp.defLine>"));
}

bool runTests(Tree t) = runTests(t);

bool ex1() {
     p = [Program] "module A {
                  '  def s = 5;
                  '}
                  'module B {
                  '  import A^1;
                  '  def x = 6;
                  '  def y = 3 + s^2;
                  '  def f =
                  '      fun x { x^9 + s^2 };
                  '}";              
    return runTests(p);
}