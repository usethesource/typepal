module examples::javaModules::Checker

import examples::javaModules::Syntax;
extend analysis::typepal::TypePal;
import String;
    
// ----  IdRoles, PathLabels and AType ---------------------------------------- 

data IdRole
    = interfaceId()
    | packageId()
    | methodId()
    | fieldId()
    | formalId()
    ;

data PathRole
    = extendsPath()
    | importPath()
    ;
 
data AType
    = interfaceType(str cname)
    | packageType(str pname)
    | methodType(AType returnType, AType argTypes)
    ;

str prettyAType(methodType(AType returnType, AType argTypes)) 
    = "method <prettyAType(returnType)>(<prettyAType(argTypes)>)";
str prettyAType(interfaceType(str cname)) = cname;

// ---- Configuration ---------------------------------------------------------

private str key_extendsRelation = "extends-relation";

data InterfaceInfo
    = interfaceInfo(FQInterfaceId iid, FQInterfaceId eiid)
    | orphanInterfaceInfo(FQInterfaceId iiid)
    ;
    
data ScopeRole
    = interfaceScope();

// getTypeNamesAndRole is needed for field selection on interface instances (by way of useViaType):
// only a interfaceType defines a type from which fields can be selected, return its name and role

tuple[list[str] typeNames, set[IdRole] idRoles] javaModulesGetTypeNamesAndRole(interfaceType(str name)){
    return <[name], {interfaceId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] javaModulesGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

// Once all extendd are known, we can define the subtype relation

TModel javaModulesPreSolver(map[str,Tree] namedTrees, TModel tm) {
	if(lrel[str,str] extendsRel := tm.store[key_extendsRelation]){
        extends = toSet(extendsRel)*;
    
        bool javaModulesSubtype(interfaceType(c1), interfaceType(c2)) = c1 == c2 ||  <c1,c2> in extends;
        default bool javaModulesSubtype(AType t1, AType t2) = t1 == t2;
    
        tm.config.isSubType = javaModulesSubtype;
        return tm;
     } else {
        throw "Inconsistent value of key_extendsRelation: <tm.store[key_extendsRelation]>";
     }
}

// Configure TypePal, after the above preparations

TypePalConfig javaModulesConfig() =
    tconfig(getTypeNamesAndRole = javaModulesGetTypeNamesAndRole,
            preSolver           = javaModulesPreSolver);
 

// ----  Collect --------------------------------------------------------------

//"package" PackageId packageId ";" "interface" InterfaceId cid "extends" FQInterfaceId ecid "{" 
//             MethodDecl* methoddecls
//        "}"
//     ;

void collect(current: (JavaModulesProgram) `<InterfaceDecl* decls>`, Collector c) {
	lrel[str,str] emptyRel = [];
    c.clearStack(key_extendsRelation);
    collect(decls, c);
}

void collect(current: (InterfaceDecl) `package <PackageId pid> ; public interface <InterfaceId iid> <Extends? extends>{ <MethodDecl* methodDecls> }`, Collector c) {
    c.define("<pid>", packageId(), current, defType(packageType("<pid>")));
    println("<pid>.<iid>");
    c.define("<pid>.<iid>", interfaceId(), current, defType(interfaceType("<pid>.<iid>")));
    c.enterScope(current);
    	scope = c.getScope();
    	if ((Extends) `extends <FQInterfaceId eiid>` <- extends) {
    		c.push(key_extendsRelation, <"<pid>.<iid>", "<eiid>">);
    		c.addPathToDef(eiid, {interfaceId()}, extendsPath());
    		c.setScopeInfo(scope, interfaceScope(), interfaceInfo([FQInterfaceId] "<pid>.<iid>", eiid));
    	}
    	else {
    		c.setScopeInfo(scope, interfaceScope(), orphanInterfaceInfo([FQInterfaceId] "<pid>.<iid>"));
    	}
    	
        
        collect(methodDecls, c);
    c.leaveScope(current);
}

/*
tuple[loc scope, InterfaceId cid, InterfaceId ecid] getCurrentInterface(Collector c){
    interfaceScopes = c.getScopeInfo(interfaceScope());
    for(<scope, scopeInfo> <- interfaceScopes){
        if(interfaceInfo(cid1, ecid1) := scopeInfo){
            return <scope, cid1, ecid1>;
        } else  {
            throw "Inconsistent info from interface scope: <scopeInfo>";
        }
    }
    
    throw  "No surrounding interface scope found";
}

void collect(current: (ConstructorDecl ) `<InterfaceId cid> <Formals formals> { <SuperCall superCall> <FieldAssignment* fieldAssignments> }`, Collector c){
    <scope, cid1, ecid1> = getCurrentInterface(c);
    if("<cid>" != "<cid1>")
        c.report(error(current, "Expected constructor name %q, found %q", "<cid1>", "<cid>"));
    c.enterScope(current);
        tp = methodType(interfaceType("<cid1>"), atypeList([interfaceType("<f.cid>") | Formal f <- formals.formals]));
        c.defineInScope(scope, "<cid>", constructorId(), current, defType(tp));
        collect(formals, superCall, fieldAssignments, c);
    c.leaveScope(current);            
}
*/

void collect(current: (Formal) `<FQInterfaceId iid> <Id id>`, Collector c){
     c.define("<id>", formalId(), current, defType(interfaceType("<iid>")));   
}
/*
void collect(fd: (FieldDecl) `<InterfaceId cid> <Id id> ;`, Collector c){
     c.define("<id>", fieldId(), id, defType(interfaceType("<cid>")));
}

*/
void collect(current: (MethodDecl) `default <FQInterfaceId cid> <Id mid> <Formals formals> { return <Expression exp> ; }`,  Collector c){   
     formal_list =  [formal | formal <- formals.formals];
     c.define("<mid>", methodId(), current, defType(formal_list + exp, AType(Solver s) { return methodType(s.getType(exp), atypeList([s.getType(formal) | formal <- formal_list])); }));
     c.enterScope(current);
         c.requireSubType(exp, interfaceType("<cid>"), error(current,  "Actual return type %t should be subtype of declared return type %t", exp, cid));
         collect(formals, exp, c);
     c.leaveScope(current);
}

void collect(current: (Formals) `( <{Formal ","}* formals> )`, Collector c){
    collect(formals, c);
}
/*
void collect(Interface cls, Collector c){
    c.use(cls.id, {interfaceId()});
}

void collect(Constructor cons, Collector c){
     c.use(cons.id, {constructorId()});
}
*/

void collect(Variable var, Collector c){
     c.use(var.id, {formalId()});
}
/*

void collect(Field fld, Collector c){
     c.use(fld.id, {fieldId()});
}
*/
void collect(Method mtd, Collector c){
     c.use(mtd.id, {methodId()});
}
/*

void collect(current: (SuperCall) `super ( <{Variable ","}* vars> );`, Collector c){
    varList = [var | var <- vars];
    <scope, cid, ecid> = getCurrentInterface(c);

    c.use(ecid, {constructorId()});
    c.calculate("super call", current, ecid + varList,
        AType (Solver s) { 
                stype = s.getType(ecid);
                if(methodType(returnType, formalType) := stype){
                   argType = atypeList([s.getType(exp) | exp <- varList]);
                   s.requireSubType(argType, formalType, error(current,  "Expected arguments %t, found %t", formalType, argType));
              } else {
                 s.report(error(current,  "Method type required in super call, found %t", stype));
              }
              return interfaceType("<ecid>");
        });
    collect(vars, c);  
}

void collect(current: (Expression) `<Expression exp> . <Field field>`, Collector c){
    c.useViaType(exp, field, {fieldId()});
    c.fact(current, field);
    collect(exp, c);
}
/

*/
void collect(current: (Expression) `<Method method> <Expressions exps>`, Collector c){
    c.use(method, {methodId()});
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
             }
         });
    collect(exps, c);
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
             }
         });
    collect(exp, exps, c);
}
/*
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
             }
            });
      collect(exps, c);
}

void collect(current: (Expression) `( <InterfaceId cid> ) <Expression exp>`, Collector c){
     castType = interfaceType("<cid>");
     c.calculate("cast `<cid>`", current, [exp],
         AType (Solver s) { 
            c.requireSubType(exp, castType, error(current, "Incorrect cast, expected subtype of %t, found %t", castType, exp));
            return castType;
            });
     collect(exp, c);
}

void collect(current: (Expression) `this`, Collector c){
    <scope, cid, ecid> = getCurrenttr(c);
    c.fact(current, interfaceType("<cid>"));             
}

void collect(current: (FieldAssignment) `this . <Field field> = <Expression exp> ;`, Collector c){
    c.use(field, {fieldId()});
    c.require("field assignment", current, [field, exp],
        void(Solver s){
            s.requireSubType(exp, field, error(current, "In assignment to field %q, expected %t, found %t", field, field, exp));
        });
    collect(exp, c);
}
*/
void collect(current: (Expressions) `( <{Expression ","}* expressions> )`, Collector c){
    collect(expressions, c);
}


void collect(current: (Expression) `0`, Collector c){
    c.fact(current, interfaceType("java.lang.Integer"));             
}