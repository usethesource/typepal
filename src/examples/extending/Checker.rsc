module examples::extending::Checker

import examples::extending::Syntax;

extend analysis::typepal::TypePal;

import IO;

// ---- Extend Typepal's ATypes, IdRoles and PathRoles ------------------------

data AType
    = structType(str name)
    | execType(str name)
    | intType()
    ;
    
data PathRole
	= importPath()
	| extendPath()
	;
    
data IdRole
    = execId()
    | structId()
    | varId()
    ;

str prettyAType(structType(name)) = "struct <name>";
str prettyAType(execType(name)) = "exec <name>";
str prettyAType(intType()) = "int";

tuple[list[str] typeNames, set[IdRole] idRoles] extendingGetTypeNamesAndRole(structType(str name)){
    return <[name], {structId()}>;
}

tuple[list[str] typeNames, set[IdRole] idRoles] extendingGetTypeNamesAndRole(execType(str name)){
    return <[name], {execId()}>;
}


default tuple[list[str] typeNames, set[IdRole] idRoles] extendingGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

Accept extendingIsAcceptablePath(TModel tm, loc defScope, loc def, Use use, PathRole pathRole) {
    res = varId() in use.idRoles  && pathRole == importPath() ? ignoreContinue() : acceptBinding();
    println("extendingIsAcceptablePath: <defScope>, <def>, <use>, <pathRole> ==\> <res>");
    return res;
}

TypePalConfig extendingConfig() =
    tconfig(getTypeNamesAndRole = extendingGetTypeNamesAndRole
            , isAcceptablePath = extendingIsAcceptablePath
           // , lookup = lookupWide
            );
 
// ---- Collect facts and constraints -----------------------------------------

void collect(current: (Program) `<StructModule* structs> <ExecModule* execs>`, Collector c){
    c.enterScope(current);
        collect(structs, c);
        collect(execs, c);
    c.leaveScope(current);
}

void collect(current:(StructModule)`struct <Id modId> { <Import* imports> <VarDecl* vars> }`, Collector c) {
    c.define("<modId>", structId(), current, defType(structType("<modId>")));
    scope = c.getScope();
    c.enterScope(current);
    	collect(imports, c);
    	collect(vars, c);
    c.leaveScope(current);
}

void collect(current:(ExecModule)`exec <Id modId> { <Import* imports> <Extend* extends> <VarDecl* vars> }`, Collector c) {
    c.define("<modId>", execId(), current, defType(execType("<modId>")));
    scope = c.getScope();
    c.enterScope(current);
    	collect(imports, c);
    	collect(extends, c);
    	collect(vars, c);
    c.leaveScope(current);
}

void collect(current:(Import)`import <Id modId>`, Collector c) {
   c.addPathToDef(modId, {structId()}, importPath());
}

void collect(current:(Extend)`extend <Id modId>`, Collector c) {
   c.addPathToDef(modId, {execId()}, extendPath());
}

void collect(current:(VarDecl)`var <Id id> : <Type ty> = <Expr e>`, Collector c) {
    collect(ty, c);
    collect(e, c);
    c.require("RHS", current, [e], void (Solver s) {
        s.requireTrue(s.getType(e) == s.getType(ty), error(e, "Expected type %t, got: %t", ty, e));
    });
    c.define("<id>", varId(), current, defType(ty));
}

void collect(current:(Type)`int`, Collector c) {
	c.fact(current, intType());
}

void collect(current:(Type)`<Id id>`, Collector c) {
	c.use(current, { structId() });
}


void collect(current:(Expr)`<Expr e>.<Id fieldName>`, Collector c) {
	collect(e, c);
	c.useViaType(e, fieldName, { varId() });
	c.fact(current, fieldName);
	c.require("Receiver", current, [e], void (Solver s) {
        s.requireTrue(s.getType(e) is structType, error(e, "Expected function type, got: %t", e));
    });
}

void collect(current:(Expr)`0`, Collector c) {
    c.fact(current, intType());
}

void collect(current:(Expr)`new <Id id>`, Collector c) {
    c.use(id, { structId() });
    c.fact(current, id);
}

void collect(current:(Expr)`<Ref r>`, Collector c) {
    collect(r, c);
}


void collect(current:(Ref)`<Id moduleName>::<Id varName>`, Collector c) {
    c.use(moduleName, { execId() });
 	c.useViaType(moduleName, varName, { varId() });
 	c.fact(current, varName);
}

void collect(current:(Ref)`<Id varName>`, Collector c) {
    c.use(varName, { varId() });
}

