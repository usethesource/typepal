@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
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
