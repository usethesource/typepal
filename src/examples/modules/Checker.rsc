@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::modules::Checker

import examples::modules::Syntax;
import IO;
import String;

extend analysis::typepal::TypePal;
extend analysis::typepal::TestFramework;

lexical ConsId =  "$" ([a-z A-Z 0-9 _] !<< [a-z A-Z _][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _])\Reserved;

data AType
	= structType(str name)
	| moduleType();
	
data IdRole
    = structId()
    | moduleId()
    ;
    
data PathRole
    = importPath()
    ;

str prettyPrintAType(structType(name)) = "structType(<name>)";
str prettyPrintAType(moduleType()) = "moduleType()";

private loc project(loc file) {
   assert file.scheme == "project";
   return |project://<file.authority>|;
}

data PathConfig = pathConfig(list[loc] srcs = [], list[loc] libs = []);

PathConfig pathConfig(loc file) {
   assert file.scheme == "project";

   p = project(file);      
 
   return pathConfig(srcs = [ p + "src/examples/modules"]);
}

private str MODULES_IMPORT_QUEUE = "__modulesImportQueue";

str getFileName((ModuleId) `<{Id "::"}+ moduleName>`) = replaceAll("<moduleName>.modules", "::", "/");

tuple[bool, loc] lookupModule(str name, PathConfig pcfg) {
    for (s <- pcfg.srcs + pcfg.libs) {
        result = (s + replaceAll(name, "::", "/"))[extension = "modules"];
        if (exists(result)) {
        	return <true, result>;
        }
    }
    return <false, |invalid:///|>;
}

void collect(current:(Import) `import <ModuleId moduleName>`, Collector c) {
    c.addPathToDef(moduleName, {moduleId()}, importPath());
    c.push(MODULES_IMPORT_QUEUE, "<moduleName>");
}

void handleImports(Collector c, Tree root, PathConfig pcfg) {
    set[str] imported = {};
    while (list[str] modulesToImport := c.getStack(MODULES_IMPORT_QUEUE) && modulesToImport != []) {
        c.clearStack(MODULES_IMPORT_QUEUE);
        for (m <- modulesToImport, m notin imported) {
            if (<true, l> := lookupModule(m, pcfg)) {
                collect(parse(#start[Program], l).top, c);
            }
            else {
                c.report(error(root, "Cannot find module %v in %v or %v", m, pcfg.srcs, pcfg.libs));
            }
            imported += m; 
        }
    }
}

// ----  Collect definitions, uses and requirements -----------------------


void collect(current: (Program) `module <ModuleId moduleName>  <Import* imports> <TopLevelDecl* decls>`, Collector c){
 	c.define("<moduleName>", moduleId(), current, defType(moduleType()));
 	c.enterScope(current); {
 		collect(imports, c);
    	collect(decls, c);
    }
    c.leaveScope(current);
}
 
void collect(current:(TopLevelDecl) `struct <Id id> { <DeclInStruct* decls> }`,  Collector c) {
     c.define("<id>", structId(), current, defType(structType("<id>")));
     
     c.enterScope(current); {
     	collect(decls, c);
    }
    c.leaveScope(current);
}

void collect(current:(DeclInStruct) `<Type ty>`,  Collector c) {
	collect(ty, c);
}    

void collect(current: (Type) `<Id name>`, Collector c){
	c.use(name, {structId()});
    
}

// ----  Examples & Tests --------------------------------
TModel modulesTModelFromTree(Tree pt){
    if (pt has top) pt = pt.top;
    c = newCollector("modules", pt, getModulesConfig());
    collect(pt, c);
    handleImports(c, pt, pathConfig(pt@\loc));
    return newSolver(pt, c.run()).run();
}

tuple[list[str] typeNames, set[IdRole] idRoles] modulesGetTypeNameAndRole(structType(str name)) = <[name], {structId()}>;
tuple[list[str] typeNames, set[IdRole] idRoles] modulesGetTypeNameAndRole(AType t) = <[], {}>;

private TypePalConfig getModulesConfig() = tconfig(
    getTypeNamesAndRole = modulesGetTypeNameAndRole
    //verbose=debug 
    //logTModel = debug
    //logAttempts = debug, 
    //logSolverIterations= debug
);


public start[Program] sampleModules(str name) = parse(#start[Program], |project://typepal/src/examples/modules/<name>.modules|);

list[Message] runModules(str name, bool debug = false) {
    Tree pt = sampleModules(name);
    TModel tm = modulesTModelFromTree(pt);
    return tm.messages;
}
 
bool testModules(int n, bool debug = false, set[str] runOnly = {}) {
    return runTests([|project://modules-core/src/lang/modules/modules<"<n>">.ttl|], #start[Program], TModel (Tree t) {
        return modulesTModelFromTree(t);
    }, runOnly = runOnly);
}

