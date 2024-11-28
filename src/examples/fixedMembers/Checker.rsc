@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
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
    c.define("<modId>", moduleId(), current, defType(moduleType("<modId>")));
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
    c.define("<id>", functionId(), current, defType(functionType("<id>")));
}


// function call

void collect(current:(Stmt)`<Id modId>.<Id funId> ();`, Collector c) {
    c.use(modId, { moduleId() });
 	c.useViaType(modId, funId, {functionId()});
}
