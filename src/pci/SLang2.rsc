module SLang2

import IO;
extend ScopeGraph;
extend Extract;
import String;

//---- Syntax ---------------------------------

layout Whitespace = [\t-\n\r\ ]+ !>> [\t-\n\r\ ];
layout Whitespace = [0-9]+[:];

lexical Id  = [a-zA-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9];
lexical IntCon = [0-9]+  !>> [0-9];
 
layout Type 
    = "int"
    | "void"
    | @use{type} Name name "^" IntCon defLine
    ;

layout Layout = Whitespace* !>> [\t-\n\r\ ];

syntax Name
    = {Id "."}+ ids !>> Id
    ;

start syntax Packages
    = @def{packages} Package+ packages
    ;
    
syntax  Package
    = @def{package} "package" Name name "{" Decl* decls "}";

syntax ClassDecl
    = @def{class} Visibility visibility "class" Name name Extends extends Implements implements "{" Decl* decls "}";

syntax InterfaceDecl
    = @def{interface} Visibility visibility "interface" Name name "{" Decl* decls "}";

syntax Visibility
    = visPackage: ()
    | visPublic: "public"
    | visPrivate: "private"
    ;
       
syntax Extends
    = empty: ()
    | "extends" Name name "^" IntCon defLine
    ;
syntax Implements
    = empty: ()
    | "implements" Name name "^" IntCon defLine
    ;
    
syntax Decl
    = ClassDecl classDecl
    | InterfaceDecl interfaceDecl
    | VarDecl varDecl
    | MethodDecl methodDecl
    ;
    
syntax VarDecl
    = @def{variable} Visibility visibility Type type Id id Init init ";"
    ;
syntax Init
    = empty: ()
    | "=" Exp exp
    ;
syntax Exp
    = @use{variable} Name name "^" IntCon defLine
    | a_int: IntCon intcon
    ;

syntax Statement
    = a_decl: Decl decl
    | a_exp: Exp exp ";"
    ;
        
syntax MethodDecl 
    = @def{method} Visibility visibility Type type Id id "(" Parameter* parameters ")" "{" Statement* statements "}";

syntax Parameter
    = @def{parameter} VarDecl varDecl
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

set[IdRole] classOrPackageId = {
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

bool isPublicVis(ScopeGraph sg, Key def)  = sg.key2fact[def].vis == publicVis();
bool isPrivateVis(ScopeGraph sg, Key def) = sg.key2fact[def].vis == privateVis();
bool isPackageVis(ScopeGraph sg, Key def) = sg.key2fact[def].vis == packageVis();

data DefFact
    = defFact(Vis vis)
    ;
    
data ScopeGraph(map[Key, DefFact] key2fact =(), 
                set[Key] packages = {},
                set[Key] classes = {}, 
                set[Key] interfaces = {}, 
                set[Key] methods = {});

ScopeGraph finalizeScopeGraph(ScopeGraph sg){
    sg.key2fact = ( defined : defFact | <Key range, Idn id, IdRole idRole, Key defined, DefFact defFact> <- sg.defines );
    reduced_defines = sg.defines<2,3>;
    sg.packages = reduced_defines[packageId()];
    sg.classes = reduced_defines[classId()];
    sg.interfaces = reduced_defines[interfaceId()];
    sg.methods = reduced_defines[methodIdRole()];
    
    return sg;
}

Key containedIn(Key def, set[Key] containers){
    for(pdef <- containers){
        if(def <= pdef){
           return pdef;
        }
    }
    throw "get <def>";
}

Key getPackage(ScopeGraph sg, Key def) = containedIn(def, sg.packages);
Key getClass(ScopeGraph sg, Key def) = containedIn(def, sg.classes);
Key getMethod(ScopeGraph sg, Key def) = containedIn(def, sg.methods);

str lastId(Name nm) = "<[id | id <- nm.ids][-1]>";
 
list[str] getIds(Name name) = ["<id>" | id <- name.ids];

// Language-specific defines   

Key define("package", SGBuilder sg, Key parent, Package d) {
    sg.define(parent, lastId(d.name), packageId(), d@\loc, defFact(publicVis())); 
    return d@\loc;
}

Key define("class", SGBuilder sg, Key parent, ClassDecl d)   {
    sg.define(parent, lastId(d.name), classId(), d@\loc, defFact(getVis(d.visibility))); 
    if(!(d.extends is empty)){
        sg.use_qual_ref(getIds(d.extends.name), d.extends.name@\loc, parent, classOrPackageId, classOrPackageId, extendsLabel(), toInt("<d.extends.defLine>"));
    }
    if(!(d.implements is empty)){
        sg.use_qual_ref(getIds(d.implements.name), d.implements.name@\loc, parent, classOrPackageId, classOrPackageId, implementsLabel(), toInt("<d.implements.defLine>"));
    }
    return d@\loc;
}

Key define("interface", SGBuilder sg, Key parent, InterfaceDecl d) { 
    sg.define(parent, lastId(d.name), interfaceId(), d@\loc, defFact(getVis(d.visibility)));
    return d@\loc;
}

Key define("method", SGBuilder sg, Key parent, MethodDecl d) { 
    sg.define(parent, "<d.id>", methodIdRole(), d@\loc, defFact(getVis(d.visibility))); 
    return d@\loc;
}

Key define("variable", SGBuilder sg, Key parent, VarDecl d) {
    sg.define(parent, "<d.id>", variableId(), d@\loc, defFact(getVis(d.visibility))); 
    return parent;
}

// Language-specific uses

void use("variable", SGBuilder sg, Key parent, Exp exp){
     sg.use_qual(getIds(exp.name), exp.name@\loc, parent, {variableId()}, classOrPackageId, toInt("<exp.defLine>"));
}

void use("type", SGBuilder sg, Key parent, Type tp){
     sg.use_qual(getIds(tp.name), tp.name@\loc, parent, {variableId()}, classOrPackageId, toInt("<tp.defLine>"));
}

Accept isAcceptableSimple(ScopeGraph sg, Key def, Use use){
    if(debug) println("isAcceptableSimple: <def>, <use>");
    res = acceptBinding();
    if(variableId() in use.idRoles){
       if(def < use.scope){
          res = use.occ.begin.line > def.begin.line ? acceptBinding() : ignoreContinue();
       }
       if(debug) println("isAcceptableSimple =\> <res>");
       return res;
    }
    
    if(classId() in use.idRoles && isPrivateVis(sg, def)){
        if(!(use.occ < def)){
          res = ignoreContinue();
        }
        if(debug) println("isAcceptableSimple =\> <res>");
        return res;
    }
    
    if(getPackage(sg, use.scope) != getPackage(sg, def) && !isPublicVis(sg, def)){
        res = ignoreSkipPath();
    }
    if(debug) println("isAcceptableSimple =\> <res>");
    return res;
}

Accept isAcceptableQualified(ScopeGraph sg, Key def, Use use){
    if(debug) println("isAcceptableQualified: <def>, <use>");
    return acceptBinding();
}

Accept isAcceptablePath(ScopeGraph sg, Key def, Use use, PathLabel pathLabel) {
    if(debug) println("isAcceptablePath: <def>, <use>, <pathLabel>");
    
    puse =  getPackage(sg, use.scope);
    pdef = getPackage(sg, def);
    if((pdef != puse && !isPublicVis(sg, def)) || (pdef == puse && isPrivateVis(sg, def))){
        if(debug) println("isAcceptablePath =\> ignoreSkipPath");
        return ignoreSkipPath();
    }
    
    if(debug) println("isAcceptablePath =\> acceptBinding");
    return acceptBinding();
}

//---- Examples -------------------------------

bool runTests(Tree t) = runTests(t);

bool ex0(){
    p = [Packages] "package H {
                   ' int y;
                   '   class A {
                  '     int x; 
                  '     int h() {i^3; j^0;}
                  '     class Y extends Z^4 {}
                  '   }
                   '}";
    return runTests(p);
}
   
bool ex1() {
    p = [Packages] "package H {
                   ' class C { 
                  '   int i;
                  '   class Z {}
                  '   class A {
                  '     int x; 
                  '     int h() {i^3; j^0;}
                  '     class Y extends Z^4 {}
                  '   }
                  '   class B extends A^5 {
                  '     int j;
                  '     int g() { x^6; 
                  '               B.x^6; }
                  '   }
                  ' }
                  '}";
    return runTests(p);
}

bool ex2(){

     p = [Packages] "package H {
                   '  class A {
                   '    void x()
                   '      { int j = i^7;
                   '        int i = 1;
                   '      }
                   '    int i = 10;
                   '  }
                   '}";
     return runTests(p);
}

bool ex3(){
                   
    p = [Packages] "package p1 {
                   '  public class A {
                   '    public class p1 {}
                   '  }
                   '  class C extends p2.B^10 {
                   '     p1.C^11 p = 0;
                   '  }
                   '}
                   'package p2 {
                   'public class B extends p1.A^2 {}
                   '   private class p1 {}
                   '}";
     return runTests(p);
}

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

bool ex5(){                
     p = [Packages] "package p1 {
                    '  public class A {}
                    '}
                    'package p2 {
                    '  class B extends p1.A^2 {}
                    '}";
    return runTests(p);
}

bool ex6(){
    p = [Packages] "package p1 {
                    '  interface A {
                    '    class D {}
                    '  }
                    '  class B extends C.D^3 {}
                    '  class C implements A^2 {}
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

