@license{
Copyright (c) 2024-2025, Swat.engineering
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation
and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
}

module examples::modules::Rename

import examples::modules::Checker;
import examples::modules::Syntax;

extend analysis::typepal::refactor::Rename;
import analysis::diff::edits::TextEdits;

import Exception;
import IO;
import Map;
import Relation;
import Set;
import util::FileSystem;
import util::Maybe;
import util::Reflective;

data RenameConfig(
    PathConfig pcfg = pathConfig()
);

public tuple[list[DocumentEdit] edits, set[Message] msgs] renameModules(list[Tree] cursor, str newName) {
    bool nameIsValid = any(ModuleId _ <- cursor)
        ? isValidName(moduleId(), newName)
        : isValidName(structId(), newName);

    if (!nameIsValid) {
        return <[], {error("Invalid name: <newName>", cursor[0].src)}>;
    }

    return rename(
        cursor
      , newName
      , rconfig(
          Tree(loc l) { return parse(#start[Program], l); }
        , modulesTModelFromTree
        , pcfg = pathConfig(srcs = [cursor[0].src.top.parent])
        , jobLabel = "Renaming \'<cursor[0]>\' to \'<newName>\' at <cursor[0].src>"
      )
    );
}

bool isValidName(moduleId(), str name) = tryParse(#ModuleId, name);
bool isValidName(structId(), str name) = tryParse(#Id, name);

set[loc] projectFiles(pathConfig(srcs = srcs)) =
    {*fs | dir <- srcs
       , fs := find(dir, "modules")};

private Maybe[tuple[IdRole, str]] analyzeUse((Import) `import <ModuleId id>`) = just(<moduleId(), "<id>">);
private Maybe[tuple[IdRole, str]] analyzeUse((DeclInStruct) `<Type id>`) = just(<structId(), "<id>">);
private default Maybe[tuple[IdRole, str]] analyzeUse(Tree _) = nothing();

private Maybe[tuple[IdRole, str]] analyzeDef((Program) `module <ModuleId id> <Import* _> <TopLevelDecl* _>`) = just(<moduleId(), "<id>">);
private Maybe[tuple[IdRole, str]] analyzeDef((TopLevelDecl) `struct <Id id> { <DeclInStruct* _> }`) = just(<structId(), "<id>">);
private default Maybe[tuple[IdRole, str]] analyzeDef(Tree _) = nothing();

set[Define] getCursorDefinitions(list[Tree] cursor, Tree(loc) getTree, TModel(Tree) getModel, Renamer r) {
    TModel tm = getModel(cursor[-1]);
    for (Tree c <- cursor) {
        if (tm.definitions[c.src]?) {
            return {tm.definitions[c.src]};
        } else {
            str cursorName = "<c>";
            set[Define] defs = {};
            for (loc f <- (tm.paths<pathRole, to>)[importPath()]) {
                Tree fTree = getTree(f);
                for (/Tree t := fTree) {
                    if (just(<idRole, cursorName>) := analyzeDef(t)) {
                        tm = getModel(fTree);
                        defs += {d | Define d:<_, cursorName, _, idRole, _, _> <- tm.defines};
                    }
                }
            }
            if (defs != {}) return defs;
        }
    }

    r.msg(error(cursor[0].src, "Could not find definition to rename."));
    return {};
}

tuple[set[loc], set[loc], set[loc]] findOccurrenceFiles(set[Define] defs, list[Tree] cursor, str newName, Tree(loc) getTree, Renamer r) {
    set[loc] defFiles = {};
    set[loc] useFiles = {};
    set[loc] newNameFiles = {};

    for (Define _:<_, name, _, idRole, _, _> <- defs) {
        for (loc f <- projectFiles(r.getConfig().pcfg)) {
            for (/Tree t := getTree(f)) {
                if (just(<idRole, str n>) := analyzeDef(t)) {
                    if (n == name) defFiles += f;
                    else if (n == newName) newNameFiles += f;
                }
                if (just(<idRole, str n>) := analyzeUse(t)) {
                    if (n == name) useFiles += f;
                    else if (n == newName) newNameFiles += f;
                }
            }
        }
    }

    return <defFiles, useFiles, newNameFiles>;
}

void renameUses(set[Define] defs, str newName, TModel tm, Renamer r) {
    // Somehow, tm.useDef is empty, so we need to use tm.uses
    rel[loc, loc] defUse = {<d, u> | <Define _:<_, id, orgId, idRole, d, _>, use(id, orgId, u, _, _)> <- defs * toSet(tm.uses)};

    for (loc u <- defUse[defs.defined]) {
        r.textEdit(replace(u, newName));
    }
}

bool tryParse(type[&T <: Tree] tp, str s) {
    try {
        parse(tp, s);
        return true;
    } catch ParseError(_): {
        return false;
    }
}
