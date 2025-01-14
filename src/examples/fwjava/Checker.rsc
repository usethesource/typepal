@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::fwjava::Checker

import examples::fwjava::Syntax;
extend analysis::typepal::TypePal;
import String;
    
// ----  IdRoles, PathLabels and AType ---------------------------------------- 

data IdRole
    = classId()
    | constructorId()
    | methodId()
    | fieldId()
    | formalId()
    ;

data PathRole
    = extendsPath()
    ;

data AType
    = classType(str cname)
    | methodType(AType returnType, AType argTypes)
    ;

str prettyAType(methodType(AType returnType, AType argTypes)) 
    = "method <prettyAType(returnType)>(<prettyAType(argTypes)>)";
str prettyAType(classType(str cname)) = cname;

// ---- Configuration ---------------------------------------------------------

private str key_extendsRelation = "extends-relation";

data ClassInfo
    = classInfo(ClassId cid, ClassId ecid)
    ;
    
data ScopeRole
    = classScope();

// getTypeNamesAndRole is needed for field selection on class instances (by way of useViaType):
// only a classType defines a type from which fields can be selected, return its name and role

tuple[list[str] typeNames, set[IdRole] idRoles] fwjGetTypeNamesAndRole(classType(str name)){
    return <[name], {classId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] fwjGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

// The only overloading that is allowed is between a class names and constructor names

bool fwjMayOverload (set[loc] defs, map[loc, Define] defines) {
    roles = {defines[def].idRole | def <- defs};
    return roles == {classId(), constructorId()};
}

// Set up the definition of the class and constructor for "Object"

 void fwjPreCollectInitialization(Tree _, Collector c){
    class_def = c.predefine("Object",  classId(), |global-scope:///|, defType(classType("Object")));
    c.predefineInScope(class_def, "Object", constructorId(), defType(methodType(classType("Object"), atypeList([]))));
}

// Once all extends are known, we can define the subtype relation

TModel fwjPreSolver(map[str,Tree] _, TModel tm) {
    if(lrel[str,str] extendsRel := tm.store[key_extendsRelation]){
        extends = toSet(extendsRel)*;
    
        bool FWJsubtype(classType(c1), classType(c2)) = c1 == c2 || c2 == "Object" || <c1,c2> in extends;
        default bool FWJsubtype(AType t1, AType t2) = t1 == t2;
    
        tm.config.isSubType = FWJsubtype;
        return tm;
     } else {
        throw "Inconsistent value of key_extendsRelation: <tm.store[key_extendsRelation]>";
     }
}

// Configure TypePal, after the above preparations

TypePalConfig fwjConfig() =
    tconfig(mayOverload         = fwjMayOverload,
            getTypeNamesAndRole = fwjGetTypeNamesAndRole,
            preSolver           = fwjPreSolver);
 

// ----  Collect --------------------------------------------------------------

void collect(current: (ClassDecl) `class <ClassId cid> extends <ClassId ecid> { <FieldDecl* fieldDecls> <ConstructorDecl constructorDecl> <MethodDecl* methodDecls> }`, Collector c) {
    c.define("<cid>", classId(), current, defType(classType("<cid>")));
    c.enterScope(current);
        c.push(key_extendsRelation, <"<cid>", "<ecid>">);
        scope = c.getScope();
        c.setScopeInfo(scope, classScope(), classInfo(cid, ecid));
        c.addPathToDef(ecid, {classId()}, extendsPath());
        collect(fieldDecls, constructorDecl, methodDecls, c);
    c.leaveScope(current);
}

tuple[loc scope, ClassId cid, ClassId ecid] getCurrentClass(Collector c){
    classScopes = c.getScopeInfo(classScope());
    for(<scope, scopeInfo> <- classScopes){
        if(classInfo(cid1, ecid1) := scopeInfo){
            return <scope, cid1, ecid1>;
        } else  {
            throw "Inconsistent info from class scope: <scopeInfo>";
        }
    }
    
    throw  "No surrounding class scope found";
}

void collect(current: (ConstructorDecl ) `<ClassId cid> <Formals formals> { <SuperCall superCall> <FieldAssignment* fieldAssignments> }`, Collector c){
    <scope, cid1, ecid1> = getCurrentClass(c);
    if("<cid>" != "<cid1>")
        c.report(error(current, "Expected constructor name %q, found %q", "<cid1>", "<cid>"));
    c.enterScope(current);
        tp = methodType(classType("<cid1>"), atypeList([classType("<f.cid>") | Formal f <- formals.formals]));
        c.defineInScope(scope, "<cid>", constructorId(), current, defType(tp));
        collect(formals, superCall, fieldAssignments, c);
    c.leaveScope(current);            
}

void collect(current: (Formal) `<ClassId cid> <Id id>`, Collector c){
     c.define("<id>", formalId(), current, defType(classType("<cid>")));   
}

void collect(fd: (FieldDecl) `<ClassId cid> <Id id> ;`, Collector c){
     c.define("<id>", fieldId(), id, defType(classType("<cid>")));
}

void collect(current: (MethodDecl) `<ClassId cid> <Id mid> <Formals formals> { return <Expression exp> ; }`,  Collector c){   
     formal_list =  [formal | formal <- formals.formals];
     c.define("<mid>", methodId(), current, defType(formal_list + exp, AType(Solver s) { return methodType(s.getType(exp), atypeList([s.getType(formal) | formal <- formal_list])); }));
     c.enterScope(current);
         c.requireSubType(exp, classType("<cid>"), error(current,  "Actual return type %t should be subtype of declared return type %t", exp, cid));
         collect(formals, exp, c);
     c.leaveScope(current);
}

void collect(current: (Formals) `( <{Formal ","}* formals> )`, Collector c){
    collect(formals, c);
}

void collect(Class cls, Collector c){
    c.use(cls.id, {classId()});
}

void collect(Constructor cons, Collector c){
     c.use(cons.id, {constructorId()});
}

void collect(Variable var, Collector c){
     c.use(var.id, {formalId(), fieldId()});
}

void collect(Field fld, Collector c){
     c.use(fld.id, {fieldId()});
}

void collect(Method mtd, Collector c){
     c.use(mtd.id, {methodId()});
}

void collect(current: (SuperCall) `super ( <{Variable ","}* vars> );`, Collector c){
    varList = [var | var <- vars];
    <scope, cid, ecid> = getCurrentClass(c);

    c.use(ecid, {constructorId()});
    c.calculate("super call", current, ecid + varList,
        AType (Solver s) { 
                stype = s.getType(ecid);
                if(methodType(_, formalType) := stype){
                   argType = atypeList([s.getType(exp) | exp <- varList]);
                   s.requireSubType(argType, formalType, error(current,  "Expected arguments %t, found %t", formalType, argType));
              } else {
                 s.report(error(current,  "Method type required in super call, found %t", stype));
              }
              return classType("<ecid>");
        });
    collect(vars, c);  
}

void collect(current: (Expression) `<Expression exp> . <Field field>`, Collector c){
    c.useViaType(exp, field, {fieldId()});
    c.fact(current, field);
    collect(exp, c);
}

void collect(current: (Expression) `<Expression exp> . <Method method> <Expressions exps>`, Collector c){
    c.useViaType(exp, method, {methodId()});
    args = [arg | arg <- exps.expressions];
    c.calculate("method call <method>", current, method + args,
         AType (Solver s) { 
            mtype = s.getType(method);
            if(methodType(returnType, formalType) := mtype){
                argType = atypeList([s.getType(arg) | arg <- args]);
                s.requireSubType(argType, formalType, error(current,  "Expected arguments %t, found %t", formalType, argType));
                return returnType;
             } else {
                s.report(error(current, "Method type required, found %t", mtype));
                return classType("UNKNOWN");
             }
         });
    collect(exp, exps, c);
}

void collect(current: (Expression) `new <Constructor cons> <Expressions exps>`, Collector c){
     c.use(cons, {constructorId()});
     args = [exp | exp <- exps.expressions];
    
     c.calculate("new `<cons>`", current, cons + args,
         AType(Solver s) { 
            ctype = s.getType(cons);
            if(methodType(returnType, formalType) := ctype){
                argType = atypeList([s.getType(arg) | arg <- args]);
                s.requireSubType(argType, formalType, error(current, "Expected constructor arguments %t, found %t", formalType, argType));
                return returnType;
             } else {
                s.report(error(current, "Constructor %q requires method type, found %t", cons, ctype));
                return classType("UNKNOWN");
             }
            });
      collect(exps, c);
}

void collect(current: (Expression) `( <ClassId cid> ) <Expression exp>`, Collector c){
     castType = classType("<cid>");
     c.calculate("cast `<cid>`", current, [exp],
         AType (Solver s) { 
            s.requireSubType(exp, castType, error(current, "Incorrect cast, expected subtype of %t, found %t", castType, exp));
            return castType;
            });
     collect(exp, c);
}

void collect(current: (Expression) `this`, Collector c){
    <scope, cid, ecid> = getCurrentClass(c);
    c.fact(current, classType("<cid>"));             
}

void collect(current: (FieldAssignment) `this . <Field field> = <Expression exp> ;`, Collector c){
    c.use(field, {fieldId()});
    c.require("field assignment", current, [field, exp],
        void(Solver s){
            s.requireSubType(exp, field, error(current, "In assignment to field %q, expected %t, found %t", field, field, exp));
        });
    collect(exp, c);
}

void collect(current: (Expressions) `( <{Expression ","}* expressions> )`, Collector c){
    collect(expressions, c);
}
