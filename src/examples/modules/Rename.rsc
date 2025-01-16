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

import analysis::typepal::refactor::Rename;
import analysis::typepal::refactor::TextEdits;

import Exception;
import IO;
import Relation;
import util::FileSystem;
import util::Maybe;

public tuple[list[DocumentEdit] edits, map[str, ChangeAnnotation] annos, set[Message] msgs] renameModules(list[Tree] cursor, str newName, set[loc] workspaceFolders) {
    bool nameIsValid = any(ModuleId _ <- cursor)
        ? isValidName(moduleId(), newName)
        : isValidName(structId(), newName);

    if (!nameIsValid) {
        return <[], (), {error("Invalid name: <newName>", cursor[0].src)}>;
    }

    set[loc] findCandidateFiles(set[Define] defs, Renamer r) =
        {*ls | loc wsFolder <- workspaceFolders, ls := find(wsFolder, "modules")};

    return rename(
        cursor
      , newName
      , Tree(loc l) { return parse(#start[Program], l); }
      , collectAndSolve
      , findDefinitions(workspaceFolders)
      , findCandidateFiles
      , renameDef
      , skipCandidate = skipCandidate
    );
}

set[Define](list[Tree], Tree(loc), TModel(Tree), Renamer) findDefinitions(set[loc] workspaceFolders) =
    set[Define](list[Tree] cursor, Tree(loc) getTree, TModel(Tree) getTModel, Renamer r) {

    TModel tm = getTModel(cursor[-1]);
    if (just(Define def) := findDef(cursor, tm)) {
        // Definition lives in this module
        return {def};
    }

    // Definition lives in another module.
    if (Tree c <- cursor
     && set[loc] defs:{_, *_} := tm.useDef[c.src]) {
        return {tm.definitions[d] | d <- defs, tm := getTModel(getTree(d.top))};
    }

    r.msg(error("No definition for name under cursor", cursor[0].src));
    return {};
};

bool tryParse(type[&T <: Tree] tp, str s) {
    try {
        parse(tp, s);
        return true;
    } catch ParseError(_): {
        return false;
    }
}

bool isValidName(moduleId(), str name) = tryParse(#ModuleId, name);
bool isValidName(structId(), str name) = tryParse(#Id, name);

bool skipCandidate(set[Define] defs, Tree modTree, Renamer r) {
    // Only if the name of the definition appears in the module, consider it a rename candidate
    set[str] names = {d.id | d <- defs};
    if (/Tree t := modTree, "<t>" in names) {
        return false;
    }
    return true;
}

Maybe[Define] findDef(list[Tree] cursor, TModel tm) {
    for (Tree t <- cursor) {
        if (tm.definitions[t.src]?) {
            return just(tm.definitions[t.src]);
        }
    }

    return nothing();
}

void renameDef(Define def, str newName, TModel tm, Renamer r) {
    // If the definition lives in this module, rename it
    if (def in tm.defines) {
        r.textEdit(replace(def.defined, newName));
    }

    // Rename any uses of the definition in this module
    str id = def.id;
    for (use(id, _, loc occ, _, set[IdRole] roles) <- tm.uses
       , def.idRole in roles) {
        r.textEdit(replace(occ, newName));
    }
}
