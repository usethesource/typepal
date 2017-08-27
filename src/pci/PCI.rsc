module pci::PCI

// Sample language with Packages, Classes and Interfaces

import IO;
import String;

extend typepal::TypePal;
extend typepal::TestFramework;

//---- Syntax ---------------------------------

lexical Whitespace = [\t-\n\r\ ];
layout Layout = Whitespace* !>> [\t-\n\r\ ];

lexical Id  = ([a-zA-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9]) \ Reserved;
lexical IntCon = [0-9]+  !>> [0-9];
lexical BoolCon = "true" | "false";

keyword Reserved 
    = "package" | "class" | "interface" | "implements" | "extends" |
      "public" | "private" |
      "bool" | "int" | "void" |
      "true" | "false"
      ;
 
syntax Type 
    = "bool"
    | "int"
    | "void"
    | Name name
    ;

syntax Name
    = {Id "."}+ ids !>> Id
    ;

start syntax Packages
    = Package+ packages
    ;
    
syntax  Package
    = Visibility visibility "package" Name name "{" Decl* decls "}";

syntax ClassDecl
    = Visibility visibility "class" Name name Extends extends Implements implements "{" Decl* decls "}";

syntax InterfaceDecl
    = Visibility visibility "interface" Name name "{" Decl* decls "}";

syntax MethodDecl 
    = Visibility visibility Type type Id id "(" ")" "{" Statement* statements "}";

syntax Visibility
    = visPackage: ()
    | "public"
    | "private"
    ;
       
syntax Extends
    = empty: ()
    | "extends" Name name
    ;
syntax Implements
    = empty: ()
    | "implements" Name name
    ;
    
syntax Decl
    = ClassDecl classDecl
    | InterfaceDecl interfaceDecl
    | VarDecl varDecl
    | MethodDecl methodDecl
    ;
    
syntax VarDecl
    = Visibility visibility Type type Id id Init init ";"
    ;
syntax Init
    = empty: ()
    | "=" Exp exp
    ;
syntax Exp
    = Name name
    | IntCon intcon
    | BoolCon boolcon
    ;

syntax Statement
    = Decl decl
    | Name name "=" Exp exp ";"
    ;
        

//---- End of Syntax --------------------------

// Declare declaration kinds
data IdRole
    = packageId()
    | classId()
    | interfaceId()
    | methodIdRole()
    | variableId()
    | labelId()
    ;

set[IdRole] classPackageInterfaceId = {
    packageId(),
    classId(),
    interfaceId()
};

data PathLabel
    = extendsLabel()
    | implementsLabel()
    ;

data Vis
    = publicVis()
    | privateVis()
    | packageVis() 
    ;

Vis getVis(Visibility v) =
    v is visPublic ? publicVis() : (v is visPrivate ? privateVis() : packageVis());   

data AType
    = boolType()
    | intType()
    | voidType()
    | methodType()
    ;

data DefInfo(Vis vis = publicVis());

bool isVis(FRModel frm, Key def, Vis vis) = frm.definitions[def].defInfo.vis == vis;
  
AType transType((Type) `bool`) = boolType();
AType transType((Type) `int`) = intType();

bool isSubType(boolType(), boolType(), FRModel frm) = true;
bool isSubType(intType(), intType(), FRModel frm) = true;
default bool isSubType(AType t1, AType t2, FRModel frm) = t1 == t2;

Key getPackage(FRModel frm, Key def) {
    for(p <- frm.packages){
        if(def <= p) return p;
    }
    throw "getPackage <def>";
}

// Add convenience info for the isAcceptable* functions

data FRModel (
    set[Key] packages = {},
    map[Key, Define] definitions = ()
);

FRModel enhanceFRModel(FRModel frm){
    frm.definitions = ( def.defined : def | Define def <- frm.defines);
    frm.packages = {d.defined | Define d <- frm .defines, d.idRole == packageId()};
    return frm;
}

str lastId(Name nm) = "<[id | id <- nm.ids][-1]>";
 
list[str] getIds(Name name) = ["<id>" | id <- name.ids];

// Language-specific defines   

Tree define(Package p, Tree scope, FRBuilder frb){
    frb.define(scope, lastId(p.name), packageId(), p, noDefInfo(vis = getVis(p.visibility)));
    return p;
}

Tree define(ClassDecl c, Tree scope, FRBuilder frb){
    frb.define(scope, lastId(c.name), classId(), c, noDefInfo(vis = getVis(c.visibility)));
    if(!(c.extends is empty)){
        frb.use_qual_ref(scope, getIds(c.extends.name), c.extends.name, classPackageInterfaceId, classPackageInterfaceId, extendsLabel());
    }
    if(!(c.implements is empty)){
        frb.use_qual_ref(scope, getIds(c.implements.name), c.implements.name,  classPackageInterfaceId, classPackageInterfaceId, implementsLabel());
    }
    return c;
}

Tree define(InterfaceDecl i, Tree scope, FRBuilder frb){
    frb.define(scope, lastId(i.name), interfaceId(), i, noDefInfo(vis = getVis(i.visibility)));
    return i;
}

Tree define(MethodDecl m, Tree scope, FRBuilder frb){
    frb.define(scope, "<m.id>", methodIdRole(), m, defInfo([m.\type], AType() { return typeof(m.\type); })[vis = getVis(m.visibility)]); 
    return m;
}

Tree define(VarDecl v, Tree scope, FRBuilder frb){
    frb.define(scope, "<v.id>", variableId(), v, defInfo([v.\type], AType() { return typeof(v.\type); })[vis = getVis(v.visibility)]);
    if(!(v.init is empty)){
        exp = v.init.exp;
        Tree texp = exp;
        Tree ttype = v.\type;
        frb.require("variable declaration", exp, [ttype, texp],
            (){ subtype(typeof(v.\type), typeof(exp), onError(v, "Declared type and initialization type should be equal")); });
    }
    return scope;
}

// Language-specific uses

void collect(t: (Type) `<Name name>`, Tree scope, FRBuilder frb){
    frb.use_qual(scope, getIds(name), name, {variableId()}, classPackageInterfaceId);
}

void collect(t: (Type) `bool`, Tree scope, FRBuilder frb){
    frb.atomicFact(t, boolType());
}
void collect(t: (Type) `int`, Tree scope, FRBuilder frb){
    frb.atomicFact(t, intType());
}

void collect(e: (Exp) `<Name name>`, Tree scope, FRBuilder frb){
    frb.use_qual(scope, getIds(name), name, {variableId()}, classPackageInterfaceId);
}
void collect(e: (Exp) `<BoolCon boolcon>`, Tree scope, FRBuilder frb){
    frb.atomicFact(boolcon, boolType());
}
void collect(e: (Exp) `<IntCon intcon>`, Tree scope, FRBuilder frb){
    frb.atomicFact(intcon, intType());
}

void collect(s: (Statement) `<Name name> = <Exp exp>;`, Tree scope, FRBuilder frb){
    frb.use_qual(scope, getIds(name), name, {variableId()}, classPackageInterfaceId);
    Tree tname = name;
    Tree texp = exp;
    frb.require("assignment", s, [tname, texp],
        () { equal(typeof(name), typeof(exp), onError(s, "Lhs <name> should have same type as rhs"));
           });
}

// Name resolution filters

Accept isAcceptableSimple(FRModel frm, Key def, Use use){
    
    println("isAcceptableSimple: id=<use.id> def=<def>, use=<use>");
    res = acceptBinding();
    
    // enforce definition before use
    if(variableId() in use.idRoles){
       if(def < use.scope){
          res = use.occ.begin.line > def.begin.line || 
                (use.occ.begin.line == def.begin.line && use.occ.begin.column > def.end.column)
                ? acceptBinding() : ignoreContinue();
       }
       println("isAcceptableSimple =\> <res>");
       return res;
    }
    
    // When definition is private, enforce that the use is local
    if((classId() in use.idRoles) && (frm.definitions[def].defInfo.vis == privateVis())){
        if(!(use.occ < def)){
          res = ignoreContinue();
        }
        println("isAcceptableSimple =\> <res>");
        return res;
    }
    
    // A cross package definition should be publicly visible
    println("package use: <getPackage(frm, use.scope)>");
    println("package def: <getPackage(frm, def)>");
    
    if(getPackage(frm, use.scope) != getPackage(frm, def) && !isVis(frm, def, publicVis())){ // Check!
        res = ignoreSkipPath();
    }
    println("isAcceptableSimple =\> <res>");
    return res;
}

Accept isAcceptableQualified(FRModel frm, Key def, Use use){
    println("isAcceptableQualified: <def>, <use> ==\> acceptBinding()");
    return acceptBinding();
}

Accept isAcceptablePath(FRModel frm, Key def, Use use, PathLabel pathLabel) {
    //println("isAcceptablePath: <def>, <use>, <pathLabel>");
    //
    //puse =  getPackage(frm, use.scope);
    //pdef = getPackage(frm, def);
    //if((pdef != puse && !isVis(frm, def, publicVis())) || (pdef == puse && isVis(frm, def, privateVis()))){
    //    if(debug) println("isAcceptablePath =\> ignoreSkipPath");
    //    return ignoreSkipPath();
    //}
    //
    //if(debug) println("isAcceptablePath =\> acceptBinding");
    return acceptBinding();
}

//---- Examples -------------------------------

private Packages sample(str name) = parse(#Packages, |project://TypePal/src/pci/<name>.pci|);
private ClassDecl sampleClassDecl(str name) = parse(#ClassDecl, |project://TypePal/src/pci/<name>.pci|);

set[Message] validatePCI(str name) = validate(extractFRModel(sample(name), newFRBuilder())).messages;

set[Message] validateClassDecl(str name) {
    m = validate(extractFRModel(sampleClassDecl(name), newFRBuilder()), isSubType=isSubType);
    iprintln(m);
    return m.messages;
}

void testPackages() {
    runTests(|project://TypePal/src/pci/packages.ttl|, #Packages, isSubType=isSubType);
}

void testClassDecl() {
    runTests(|project://TypePal/src/pci/classdecl.ttl|, #ClassDecl, isSubType=isSubType);
}

//test P8 [[
//    package p1 {
//        public class A {
//            public class p1 {}
//        }
//        class C extends p2.B {
//            p1.C p = 0;
//        }
//    }
//    package p2 {
//        public class B extends p1.A {}
//        private class p1 {}
//    }
//]]
bool ex4(){                
     p = [Packages] "package p1 {
                   '  public interface B {
                   '    public class C {}
                   '  }
                   '  public class A {
                   '    class C {}
                   '  }
                   '  class D extends p2.C ^13{
                   '     C^0 c;
                   '  }
                   '}
                   'package p2 {
                   'public class C extends p1.A^5
                   '               implements p1.B^2 {}
                   '}";
     return runTests(p);
}

bool ex7(){

    p = [Packages] "package p1 {
                    '  class CC {}
                    '  class C1 extends C2.BB^7 {
                    '    class AA  extends CC^2 {}
                    '  }
                    '  class C2 extends C1.AA^4 {
                    '    class BB extends CC^2 {}
                    '  }
                    '}";
    return runTests(p);
}

