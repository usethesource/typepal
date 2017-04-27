module modlang::ModLang

extend Constraints;
extend TestFramework;

// ----  ModLang syntax ----------------------------------

lexical Id      = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical ModId   = ([A-Z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Integer = [0-9]+ ; 
lexical String = "\"" ![\"]*  "\"";

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
    = "module" ModId mid  "{" Decl* decls "}"
    ;
syntax Decl
    = ImportDecl importDecl
    | VarDecl varDecl
    ;
syntax ImportDecl
    = "import" ModId mid ";"
    ;

syntax VarDecl
    = "def" Id id "=" Expression expression ";"
    ;
     
syntax Expression 
   = Id id
   | Integer intcon 
   | String strcon
   | bracket "(" Expression e ")"     
   | abstraction: "fun" Id id "{" Expression exp "}"
   | application: Expression exp1 "(" Expression exp2  ")" 
   | left Expression exp1 "*" Expression exp2 
   > left Expression exp1 "+" Expression exp2 
   ;

// ----  IdRoles, PathLabels and AType ------------------- 
     
data IdRole
    = moduleId()
    | variableId()
    | parameterId()
    ;
    
data PathLabel
    = importsLabel()
    ;

data AType   
    = intType()                                     // int type
    | strType()                                     // str type
    | functionType(AType from, AType to)            // function type
    ;
    
str AType2String(intType()) = "`int`";
str AType2String(strType()) = "`str`";

// ----  Def/Use -----------------------------------------

Tree define(ModuleDecl md, Tree scope, SGBuilder sg)     {
    sg.define(scope, "<md.mid>", moduleId(), md.mid, noDefInfo());
    return scope;
}

Tree define(e: (Expression) `fun <Id id> { <Expression body> }`, Tree scope, SGBuilder sgb) {   
    sigma1 = sgb.newTypeVar(e); 
    sigma2 = sgb.newTypeVar(e);
    sgb.define(scope, "<id>", parameterId(), id, defInfo(sigma1));
    sgb.fact(e, functionType(sigma1, sigma2));
    sgb.fact(body, sigma2);
    return scope;
}

Tree define(vd: (VarDecl) `def <Id id> = <Expression expression> ;`, Tree scope, SGBuilder sg)     {
    sg.define(scope, "<id>", variableId(), id, defInfo(typeof(expression))); 
    return expression;
}

void use(ImportDecl d, Tree scope, SGBuilder sg){
    sg.use_ref(scope, "<d.mid>", d.mid, {moduleId()}, importsLabel(), 0);
}

void use(exp: (Expression) `<Id name>`, Tree scope, SGBuilder sg){
    println("Use: <name>, <scope>");
    sg.use(scope, "<name>", name, {variableId(), parameterId()}, 0);
}

// ----  Requirements ------------------------------------

void require(e: (Expression) `<Expression exp1>(<Expression exp2>)`, SGBuilder sgb) { 
    sgb.require("application", e, 
                [ match(functionType(tau(1), tau(2)), typeof(exp1), onError(exp1, "Function type expected")), 
                  equal(typeof(exp2), tau(1), onError(exp2, "Incorrect type of actual parameter")),
                  fact(e, tau(2)) 
                ]);
}

void require(e: (Expression) `<Expression lhs> + <Expression rhs>`, SGBuilder sgb){
     sgb.overload("addition", e, 
                  [lhs, rhs], [<[intType(), intType()], intType()>, <[strType(), strType()], strType()>],
                  onError(e, "No version of + exists for given argument types"));
}

void require(e: (Expression) `<Expression lhs> * <Expression rhs>`, SGBuilder sgb){
     sgb.require("multiplication", e, 
                 [ equal(typeof(lhs), intType(), onError(lhs, "Lhs of *")),
                   equal(typeof(rhs), intType(), onError(rhs, "Rhs of *")),
                   fact(e, intType())
                 ]);
}

void require(e: (Expression) `( <Expression exp> )`, SGBuilder sgb){
     sgb.fact(e, typeof(exp));
}

void require(e: (Expression) `<String string>`, SGBuilder sgb){
    sgb.fact(e, strType());
}

void require(e: (Expression) `<Integer intcon>`, SGBuilder sgb){
    sgb.fact(e, intType());
}

// ---- Refine use/def: enforce def before use -----------

Accept isAcceptableSimple(ScopeGraph sg, Key def, Use use){

    res = variableId() in use.idRoles
           && def < use.scope 
           && !(use.occ.offset >= def.offset)
           ? ignoreContinue()
           : acceptBinding();
    println("isAcceptable: <def>, <use> ==\> <res>");
    return res;
}

// ----  Examples & Tests --------------------------------

private Program sample(str name) = parse(#Program, |project://TypePal/src/modlang/<name>.modlang|);

set[Message] validateModLang(str name) = validate(extractScopesAndConstraints(sample(name)));

void testModLang() {
    runTests(|project://TypePal/src/modlang/tests.ttl|, #Program);
}