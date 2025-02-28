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

module examples::modfun::Rename

import examples::modfun::Checker;
import examples::modfun::Syntax;

extend analysis::typepal::refactor::Rename;
import analysis::typepal::refactor::TextEdits;

import Exception;
import IO;
import List;
import Map;
import Relation;
import util::FileSystem;
import util::Maybe;

data RenameConfig(
    set[loc] srcs = {}
);

public tuple[list[DocumentEdit] edits, set[Message] msgs] renameModules(list[Tree] cursor, str newName) {
    bool nameIsValid = any(ModId _ <- cursor)
        ? isValidName(moduleId(), newName)
        : isValidName(variableId(), newName);

    if (!nameIsValid) {
        return <[], {error("Invalid name: <newName>", cursor[0].src)}>;
    }

    return rename(
        cursor
      , newName
      , rconfig(
          Tree(loc l) { return parse(#start[ModFun], l); }
        , TModel(Tree pt) { return collectAndSolve(pt, config = tconfig(mayOverload = bool(set[loc] defs, map[loc, Define] defines) { return true; })); }
        , srcs = {cursor[0].src.top.parent}
        , jobLabel = "Renaming \'<cursor[0]>\' to \'<newName>\' at <cursor[0].src>"
      )
    );
}

private Maybe[tuple[IdRole, str]] analyzeUse((ImportDecl) `import <ModId id>;`) = just(<moduleId(), "<id>">);
private Maybe[tuple[IdRole, str]] analyzeUse((Expression) `<Id id>`) = just(<variableId(), "<id>">);
private default Maybe[tuple[IdRole, str]] analyzeUse(Tree _) = nothing();

private Maybe[tuple[IdRole, str]] analyzeDef((ModuleDecl) `module <ModId id> { <Decl* _> }`) = just(<moduleId(), "<id>">);
private Maybe[tuple[IdRole, str]] analyzeDef((VarDecl) `def <Id id> : <Type _> = <Expression _>;`) = just(<variableId(), "<id>">);
private default Maybe[tuple[IdRole, str]] analyzeDef(Tree _) = nothing();

set[Define] getCursorDefinitions(list[Tree] cursor, Tree(loc) getTree, TModel(Tree) getModel, Renamer r) {
    TModel tm = getModel(cursor[-1]);
    for (Tree c <- cursor) {
        if (tm.definitions[c.src]?) {
            return {tm.definitions[c.src]};
        } else {
            str cursorName = "<c>";
            set[Define] defs = {};
            for (referToDef(use(modId, _, _, _, {moduleId(), *_}), importPath()) <- tm.referPaths
               , loc f := cursor[0].src.top.parent + "<modId>.mfun") {
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

    r.error(cursor[0].src, "Could not find definition to rename.");
    return {};
}

tuple[set[loc], set[loc]] findOccurrenceFiles(set[Define] defs, list[Tree] cursor, Tree(loc) getTree, Renamer r) {
    set[loc] defFiles = {};
    set[loc] useFiles = {};

    for (Define _:<_, name, _, idRole, _, _> <- defs) {
        for (loc srcFolder <- r.getConfig().srcs
           , loc f <- find(srcFolder, "mfun")) {
            for (/Tree t := getTree(f)) {
                if (just(<idRole, name>) := analyzeDef(t)) defFiles += f;
                if (just(<idRole, name>) := analyzeUse(t)) useFiles += f;
            }
        }
    }

    return <defFiles, useFiles>;
}

tuple[set[loc] defFiles, set[loc] useFiles] findOccurrenceFiles(set[Define] defs, list[Tree] cursor, Tree(loc) getTree, Renamer r) {
    set[loc] defFiles = {};
    set[loc] useFiles = {};

    for (Define _: <_, name, _, idRole, _, _> <- defs) {
        for (loc srcFolder <- r.getConfig().srcs
           , loc f <- find(srcFolder, "mfun")) {
            Tree t = getTree(f);

            visit(t) {
                case (ModuleDecl) `module <ModId id> { <Decl* _> }`: {
                    if ("<id>" == name) {
                        defFiles += f;
                    }
                }
                case (ImportDecl) `import <ModId id>;`: {
                    if ("<id>" == name) {
                        useFiles += f;
                    }
                }
                case (VarDecl) `def <Id id> : <Type _> = <Expression _>;`: {
                    if ("<id>" == name) {
                        defFiles += f;
                    }
                }
                case (Expression) `<Id id>`: {
                    if ("<id>" == name) {
                        useFiles += f;
                    }
                }
            }
        }
    }

    return <defFiles, useFiles>;
}

bool tryParse(type[&T <: Tree] tp, str s) {
    try {
        parse(tp, s);
        return true;
    } catch ParseError(_): {
        return false;
    }
}

bool isValidName(moduleId(), str name) = tryParse(#ModId, name);
bool isValidName(variableId(), str name) = tryParse(#Id, name);

set[Define] findAdditionalDefinitions(set[Define] cursorDefs, Tree _, TModel tm, Renamer _) {
    set[Define] overloads = {};
    for (d <- tm.defines
      && d.idRole in cursorDefs.idRole
      && d.id in cursorDefs.id
      && d.defined notin cursorDefs.defined) {
        if (tm.config.mayOverload(cursorDefs.defined + d.defined, tm.definitions)) {
            overloads += d;
        }
    }
    return overloads;
}

void renameUses(set[Define] defs, str newName, TModel tm, Renamer r) {
    // Somehow, tm.useDef is empty, so we need to use tm.uses
    rel[loc, loc] defUse = {<d, u> | <Define _:<_, id, orgId, idRole, d, _>, use(id, orgId, u, _, _)> <- defs * toSet(tm.uses)};

    for (loc u <- defUse[defs.defined]) {
        r.textEdit(replace(u, newName));
    }
}
