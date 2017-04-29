module fj::FJ

// Featherweight Java

extend ScopeGraph;
extend Constraints;
extend ExtractScopesAndConstraints;
extend TestFramework;
import ParseTree;
import String;

// ----  FJ syntax ---------------------------------------

lexical ClassId  = ([A-Z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Id  = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Integer = [0-9]+ !>> [0-9]; 

keyword Reserved = "class" | "extends" | "super" | "this" | "return";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "%" ![%]+ "%"
   | @category="Comment" ws3: "%%" ![\n]* $
   ;
   
syntax Program
    = ClassDecl* classdecls
    ;
    
syntax ClassDecl
    = "class" ClassId cid "extends" ClassId ecid "{" 
              FieldDecl* fielddecls
              ConstructorDecl constructordecl
              MethodDecl* methoddecls
        "}"
     ;

syntax FieldDecl
    = ClassId cid Id id ";"
    ;

syntax ConstructorDecl
    =  ClassId cid Formals formals "{"
            SuperCall
            FieldAssignment* fieldAssignments
       "}"
    ;

syntax SuperCall
    = "super" "(" {Field ","}* fields ")" ";"
    ;
    
syntax Formal
    =  ClassId cid Id id
    ;
    
syntax Formals
    = "(" {Formal ","}* formals ")"
    ;
          
syntax MethodDecl
    = ClassId cid Id mid Formals formals "{" "return" Expression exp ";" "}"
    ;
    
syntax Expression
    = Variable var
    | Expression exp "." Field field
    | Expression exp "." Method method Expressions exps
    | "new" Constructor constructor Expressions exps
    | "(" Class class ")" Expression exp
    | "this"
    ;

syntax Constructor
    = ClassId id
    ;
syntax Class
    = ClassId id
    ;
    
syntax Variable
    = Id id
    ;
 
syntax Field
    = Id id
    ;

syntax Method
    = Id id
    ;
           
syntax Expressions
    = "(" {Expression ","}* expressions ")"
    ;   

syntax FieldAssignment
    = "this" "." Field field "=" Expression exp ";"
    ;   
    
// ----  IdRoles, PathLabels and AType ------------------- 

data IdRole
    = classId()
    | constructorId()
    | methodId()
    | fieldId()
    | formalId()
    ;

data PathLabel
    = extendsLabel()
    ;

data AType
    = classType(Use use)
    | methodType(AType returnType, list[AType] argTypes)
    ;

AType classType(Tree scope, Tree cname, SGBuilder sgb) {
    sgb.use(scope, cname, {classId()}, 0);
    return classType(use("<cname>", cname@\loc, scope@\loc, {classId()}));
}

str AType2String(classType(Use use)) = "<use.id>";
str AType2String(methodType(AType returnType, list[AType] argTypes)) 
    = "`method <AType2String(returnType)>(<intercalate(", ", [AType2String(a) | a <- argTypes])>)`";

// ---- isSubtype

bool isSubtype(AType atype1, AType atype2, ScopeGraph sg){
    if(c1: classType(Use use1) := atype1 && c2: classType(Use use2) := atype2){
        //println("isSubtype: <AType2String(c1)>, <AType2String(c2)>");
        try {
            def1 = lookup(sg, use1);
            def2 = lookup(sg, use2);
            
            res = def1 == def2 || existsPath(sg, def1, def2, extendsLabel());
            //println("isSubtype: <def1>, <def2> ==\> <res>");
            return res;
        } catch noKey: {
            //println("isSubtype:  <use1>, <use2> ==\> false");
            return false;
        }
    } else
    if(m1: methodType(AType returnType1, list[AType] argTypes1) := atype1 &&
       m2: methodType(AType returnType2, list[AType] argTypes2) := atype2){
        //println("isSubtype: <AType2String(m1)>, <AType2String(m2)>");
        return isSubtype(returnType1, returnType2, sg) &&
               isSubtype(argTypes1, argTypes2, sg);
    }
    return atype1 == atype2;
}

bool isSubtype(list[AType] atypes1, list[AType] atypes2, ScopeGraph sg)
    = size(atypes1) <= size(atypes2) &&
      (isEmpty(atypes1) || all(int i <- index(atypes1), isSubtype(atypes1[i], atypes2[i], sg)));

// ----  Initialize --------------------------------------  

SGBuilder initialize(Tree tree, SGBuilder sgb){
    sgb.define(tree, "Object", classId(), tree, noDefInfo());
    return sgb;
} 

// ----  Def/Use -----------------------------------------

Tree define(ClassDecl cd, Tree scope, SGBuilder sgb)     {
    sgb.define(scope, "<cd.cid>", classId(), cd.cid, noDefInfo());
    sgb.use_ref(scope, cd.ecid, {classId()}, extendsLabel(), 0);
    return cd;
}

Tree define(cd: (ConstructorDecl) `<ClassId cid> <Formals formals> {
                                  '<SuperCall super>
                                  '<FieldAssignment* fieldAssignments>
                                  '}`, Tree scope, SGBuilder sgb){
    argTypes = [classType(scope, f.cid, sgb) | Formal f <- formals.formals];
    sgb.define(scope, "<cid>", constructorId(), cid, defInfo(methodType(classType(scope, cid, sgb), argTypes)));
    return cd;                      
}

Tree define(fm: (Formal) `<ClassId cid> <Id id>`, Tree scope, SGBuilder sgb){
    sgb.define(scope, "<id>", formalId(), id, defInfo(classType(scope, cid, sgb)));
    return scope;
}

Tree define(fd: (FieldDecl) `<ClassId cid> <Id id> ;`, Tree scope, SGBuilder sgb){
    sgb.define(scope, "<id>", fieldId(), id, defInfo(classType(scope, cid, sgb)));
    return scope;
}

Tree define(md: (MethodDecl) `<ClassId cid> <Id mid> <Formals formals> { return <Expression exp> ; }`, Tree scope,  SGBuilder sgb){    
    argTypes = [classType(scope, f.cid, sgb) | Formal f <- formals.formals];
    resType = classType(scope, cid, sgb);
    sgb.define(scope, "<mid>", methodId(), mid, defInfo(methodType(resType, argTypes)));
    sgb.require("method", md,
        [subtype(typeof(exp), resType, onError(md, "Actual return type should be subtype of declared return type"))
        ]);
    return md;
}

void use(Class c, Tree scope, SGBuilder sgb){
    sgb.use(scope, c.id, {classId()}, 0);
}

void use(Constructor c, Tree scope, SGBuilder sgb){
    sgb.use(scope, c.id, {constructorId()}, 0);
}

void use(Variable var, Tree scope, SGBuilder sgb){
    sgb.use(scope, var.id, {formalId(), fieldId()}, 0);
}

void use(Field fld, Tree scope, SGBuilder sgb){
    sgb.use(scope, fld.id, {fieldId()}, 0);
}

void use(Method mtd, Tree scope, SGBuilder sgb){
    sgb.use(scope, mtd.id, {methodId()}, 0);
}

// ----  Requirements ------------------------------------

void require(e: (Expression) `<Expression exp> . <Field field>`, SGBuilder sgb){
    if("<exp>" == "this"){
        sgb.fact(e, typeof(field.id));
    } else {
        sgb.fact(e, typeof(exp, field.id));
    }
}

// add methodCall

void require(e: (Expression) `new <Constructor cons> <Expressions exps>`, Tree scope, SGBuilder sgb){
    returnType = classType(scope, cons.id, sgb);
    argTypes = [ typeof(exp) | exp <- exps.expressions ];
    
    sgb.require("new", e,
        [ subtype(methodType(returnType, argTypes), typeof(cons), onError(e, "Incorrect constructor arguments")),
          fact(e, returnType) 
        ]);
}

void require(e: (Expression) `( <ClassId cid> ) <Expression exp>`, Tree scope, SGBuilder sgb){
    castType = classType(scope, cid, sgb);
    sgb.require("cast", e,
        [ subtype(typeof(exp), castType, onError(e, "Incorrect cast")),
          fact(e, castType) 
        ]);
}
/*
  = Variable var
    | Expression exp "." Field field
    | Expression exp "." Method method Expressions exps
    | "new" ClassId cid Expressions exps
    | "(" ClassId cid ")" Expression exp
    | "this"
*/
// ----  Examples & Tests --------------------------------

value main(){
    //p = 
    //[ClassDecl] "class A extends Object {
    //        '   A() { super(); }
    //        '}";
    p =
    [ClassDecl] "class Pair extends Object {
            '   Object fst;
            '   Object snd;
            '   Pair(Object fst, Object snd){
            '       super(); this.fst = fst; this.snd = snd;
            '   }
            '   Pair setfst(Object newfst){
            '       return new Pair(newfst, this.snd);
            '   }
            '}";
    return p;
}

private Program sample(str name) = parse(#Program, |project://TypePal/src/fj/<name>.fj|);

set[Message] validateFJ(str name) = validate(extractScopesAndConstraints(sample(name)));

void testFJ() {
    runTests(|project://TypePal/src/fj/tests.ttl|, #Program);
}