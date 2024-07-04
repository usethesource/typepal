module examples::fixedMembers::Checker

import examples::fixedMembers::Syntax;
extend analysis::typepal::TypePal;

// ---- Extend Typepal's ATypes, IdRoles and PathRoles ------------------------

data AType
    = moduleType(str name)
    | functionType(str name)
    ;
    
data PathRole
	= importPath();
    
data IdRole
    = moduleId()
    | functionId()
    ;

str prettyAType(functionType(name)) = "function <name>"; 
str prettyAType(moduleType(name)) = "module <name>";

tuple[list[str] typeNames, set[IdRole] idRoles] fixedMembersGetTypeNamesAndRole(moduleType(str name)){
    return <[name], {moduleId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] fixedMembersGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

TypePalConfig fixedMembersConfig() =
    tconfig(getTypeNamesAndRole = fixedMembersGetTypeNamesAndRole);

 
// ---- Collect facts and constraints -----------------------------------------

void collect(current: (Program) `<Module* modules>`, Collector c){
    c.enterScope(current);
        collect(modules, c);
    c.leaveScope(current);
}

void collect(current:(Module)`module <Id modId> <Import* imports> { <Function* funs> <Stmt* stmts>}`, Collector c) {
    c.define(modId, moduleId(), current, defType(moduleType("<modId>")));
    c.enterScope(current);
    	collect(imports, c);
    	collect(funs, c);
        collect(stmts, c);
    c.leaveScope(current);
}

void collect(current:(Import)`import <Id modId>;`, Collector c) {
   c.addPathToDef(modId, {moduleId()}, importPath());
}

void collect(current:(Function)`fun <Id id> { }`, Collector c) {
    c.define(id, functionId(), current, defType(functionType("<id>")));
}


// function call

void collect(current:(Stmt)`<Id modId>.<Id funId> ();`, Collector c) {
    c.use(modId, { moduleId() });
 	c.useViaType(modId, funId, {functionId()});
}
