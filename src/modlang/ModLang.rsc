module modlang::ModLang

extend ExtractFRModel;
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
//   | @category="Comment" ws3: "{" ![\n}]*  "}"$
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
    
str AType2String(intType()) = "int";
str AType2String(strType()) = "str";

// ----  Define --------------------------------------------------------

Tree define(ModuleDecl md, Tree scope, FRBuilder sg) {
     sg.define(scope, "<md.mid>", moduleId(), md.mid, noDefInfo());
     return scope;
}

Tree define(e: (Expression) `fun <Id id> { <Expression body> }`, Tree scope, FRBuilder frb) {   
     sigma1 = frb.newTypeVar(e); 
     sigma2 = frb.newTypeVar(e);
     frb.define(scope, "<id>", parameterId(), id, defInfo(sigma1));
     frb.atomicFact(e, functionType(sigma1, sigma2));
     frb.atomicFact(body, sigma2);
     return scope;
}

Tree define(vd: (VarDecl) `def <Id id> = <Expression expression> ;`, Tree scope, FRBuilder sg)     {
     sg.define(scope, "<id>", variableId(), id, defInfo([expression], AType(){ return typeof(expression); })); // <<<
     return expression;
}

// ---- Collect uses & requirements ------------------------------------

void collect(ImportDecl d, Tree scope, FRBuilder sg){
     sg.use_ref(scope, d.mid, {moduleId()}, importsLabel(), 0);
}

void collect(exp: (Expression) `<Id name>`, Tree scope,  FRBuilder sg){
     println("Use: <name>, <scope>");
     sg.use(scope, name, {variableId(), parameterId()}, 0);
}

void collect(e: (Expression) `<Expression exp1>(<Expression exp2>)`, Tree scope, FRBuilder frb) { 
     tau1 = frb.newTypeVar(e); 
     tau2 = frb.newTypeVar(e); 
     frb.require("application", e, [exp1, exp2],
         () { if(unify(functionType(tau1, tau2), typeof(exp1))){ 
                 unify(typeof(exp2), tau1, onError(exp2, "Incorrect type of actual parameter"));
                 fact(e, tau2);   
              } else {
                 onError(exp1, "Function type expected");
              }
            });
}

void collect(e: (Expression) `<Expression lhs> + <Expression rhs>`, Tree scope, FRBuilder frb){
     frb.overload("addition", e, [lhs, rhs],
         AType () { targs = listType([typeof(lhs), typeof(rhs)]);
                    if(unify(targs, listType([intType(), intType()]))) return intType();
                    if(unify(targs, listType([strType(), strType()]))) return strType();
                    reportError(e, "No version of + is applicable", [lhs, rhs]);
                  });
}

void collect(e: (Expression) `<Expression lhs> * <Expression rhs>`, Tree scope, FRBuilder frb){
     frb.require("multiplication", e, [lhs, rhs],
         () { unify(typeof(lhs), intType(), onError(lhs, "Lhs of *"));
              unify(typeof(rhs), intType(), onError(rhs, "Rhs of *"));
              fact(e, intType());
            });
}

void collect(e: (Expression) `( <Expression exp> )`, Tree scope, FRBuilder frb){
     frb.fact(e, [exp], AType() { return typeof(exp); } );
}

void collect(e: (Expression) `<String string>`, Tree scope, FRBuilder frb){
     frb.atomicFact(e, strType());
}

void collect(e: (Expression) `<Integer intcon>`, Tree scope, FRBuilder frb){
     frb.atomicFact(e, intType());
}

// ---- Refine use/def: enforce def before use -----------

Accept isAcceptableSimple(ScopeGraph sg, Key def, Use use){
    return variableId() in use.idRoles
           && def < use.scope 
           && !(use.occ.offset >= def.offset)
           ? ignoreContinue()
           : acceptBinding();
}

// ----  Examples & Tests --------------------------------

private Program sample(str name) = parse(#Program, |project://TypePal/src/modlang/<name>.modlang|);

set[Message] validateModLang(str name) = validate(extractScopesAndConstraints(sample(name), makeFRBuilder()));

void testModLang() {
    runTests(|project://TypePal/src/modlang/tests.ttl|, #Program);
}