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

alias RenameRequest = tuple[list[Tree] cursor, str newName, set[loc] workspaceFolders];

@memo{expireAfter(minutes=1), maximumSize(50)}
Tree parseLoc(loc l) {
    return parse(#start[Program], l);
}

@memo{expireAfter(minutes=1), maximumSize(50)}
TModel tmodelForLoc(loc l) {
    return collectAndSolve(parseLoc(l));
}

public tuple[list[DocumentEdit] edits, map[str, ChangeAnnotation] annos, set[Message] msgs] renameModules(RenameRequest request) {
    RenameConfig config = rconfig(
        parseLoc
      , tmodelForLoc
      , reportCollectCycles = true
    );

    RenameSolver renamer = newSolverForConfig(config);
    initRename(renamer, request);
    return renamer.run();
}

data RenameState
    = checkCandidate(Define d, RenameRequest req)
    | findDefinition(RenameRequest req)
    | rename(Define d, RenameRequest req)
    ;

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

void initRename(RenameSolver renamer, RenameRequest req) {
    bool nameIsValid = any(ModuleId _ <- req.cursor)
        ? isValidName(moduleId(), req.newName)
        : isValidName(structId(), req.newName);
    
    if (!nameIsValid) {
        throw "Invalid name: <req.newName>";
    }
    
    // Find definition of name under cursor
    loc fileUnderCursor = req.cursor[0].src.top; 
    renamer.collectTModel(fileUnderCursor, renameByModel, findDefinition(req));
}

void renameByTree(checkCandidate(Define d, RenameRequest req), Tree modTree, RenameSolver renamer) {
    println("Checking <modTree.src.top> for occurrences of \'<d.id>\'");
    // Only if the name of the definition appears in the module, consider it a rename candidate
    if (/Tree t := modTree, "<t>" == d.id) {
        renamer.collectTModel(modTree.src.top, renameByModel, rename(d, req));
    }
}

default void renameByTree(RenameState state, Tree _, RenameSolver _) {
    throw "Not implemented: `renameByTree` for state <describeState(state)>";
}

Maybe[Define] findDef(list[Tree] cursor, TModel tm) {
    for (Tree t <- cursor) {
        if (tm.definitions[t.src]?) {
            return just(tm.definitions[t.src]);
        }
    }

    return nothing();
}

void renameByModel(state:findDefinition(RenameRequest req), TModel tm, RenameSolver renamer) {
    println("Looking for defintion in <tm.modelName>");
    if (just(Define def) := findDef(req.cursor, tm)) {
        // Definition lives in this module
        // Check for occurrences of the definition name in all other files
        for (loc wsFolder <- req.workspaceFolders, loc m <- find(wsFolder, "modules")) {
            renamer.collectParseTree(m, renameByTree, checkCandidate(def, req));
        }
    } else {
        // Definition lives in another module.
        // Load that first, and continue from there
        if (Tree c <- req.cursor
         && set[loc] defs := tm.useDef[c.src]
         && defs != {}) {
            for (loc d <- defs) {
                renamer.collectTModel(d.top, renameByModel, state);
            }
        }
    }
}

void renameByModel(rename(Define d, RenameRequest req), TModel tm, RenameSolver renamer) {
    println("Renaming all references to <d.defined> in <tm.modelName>");

    // If the definition lives in this module, rename it
    if (tm.definitions[d.defined]?) {
        println("++ Definition in this module; renaming <d.defined>");
        renamer.textEdit(replace(d.defined, req.newName));
    }

    // Rename any uses of the definition in this module
    str id = d.id;
    set[IdRole] roles = {d.idRole};
    for (use(id, _, loc occ, _, roles) <- tm.uses) {
        println("++ Use in this module; renaming <occ>");
        renamer.textEdit(replace(occ, req.newName));
    }
}

default void renameByModel(RenameState state, TModel _, RenameSolver _) {
    throw "Not implemented: `renameByModel` for state <describeState(state)>";
}
