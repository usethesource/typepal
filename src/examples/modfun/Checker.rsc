module examples::modfun::Checker

// Modular Functional language with declared types (an extension of Fun)

import examples::modfun::Syntax;
extend examples::fun::Checker;

// ----  IdRoles, PathLabels and AType ---------------------------------------- 
     
data AType
    = moduleType(str name)
    ;
str prettyAType(moduleType(str name)) = "module(<name>)";
    
data IdRole
    = moduleId()
    ;
    
data PathRole
    = importPath()
    ;
    
// ----  Collect facts & constraints ------------------------------------------

void collect(current: (ModuleDecl) `module <ModId mid> { <Decl* decls> }`, Collector c) {
     c.define("<mid>", moduleId(), mid, defType(moduleType("<mid>")));
     //c.enterScope(current);
        collect(decls, c);
     //c.leaveScope(current);
}

void collect(current: (ImportDecl) `import <ModId mid> ;`, Collector c){
     c.addPathToDef(mid, {moduleId()}, importPath());
}

void collect(current: (VarDecl) `def <Id id> : <Type tp> = <Expression expression> ;`, Collector c)     {
     c.define("<id>", variableId(), id, defType(tp));
     c.requireEqual(tp, expression, error(current, "Expected initializing expression of type %t, found %t", expression, tp));
     collect(tp, expression, c);
}
