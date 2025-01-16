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
module examples::pico::Rename

import examples::pico::Syntax;
extend examples::pico::Checker;

import analysis::typepal::TModel;

extend analysis::typepal::refactor::Rename;

import Exception;
import IO;
import Relation;
import util::FileSystem;

data Tree;

alias RenameRequest = tuple[list[Tree] cursor, str newName/*, set[loc] workspaceFolders*/];

data RenameState
    = findDefinition(RenameRequest req)
    | rename(IdRole role, loc def, str newName)
    ;

@memo{expireAfter(minutes=1), maximumSize(50)}
Tree parseLoc(loc l) {
    return parse(#start[Program], l);
}

@memo{expireAfter(minutes=1), maximumSize(50)}
TModel tmodelForLoc(loc l) {
    return collectAndSolve(parseLoc(l));
}

public tuple[list[DocumentEdit] edits, map[str, ChangeAnnotation] annos, set[Message] msgs] renamePico(RenameRequest request) {
    RenameConfig config = rconfig(
        parseLoc
      , tmodelForLoc
      , reportCollectCycles = true
    );

    RenameSolver solver = newSolverForConfig(config);
    initSolver(solver, request);
    return solver.run();
}

void initSolver(RenameSolver solver, RenameRequest req) {
    if (!isValidName(req.newName)) {
        // gooi errors
        solver.msg(error("Not a valid name: \'<req.newName>\'!"));
        return;
    }

    loc currentModule = req.cursor[0].src.top;
    solver.collectTModel(currentModule, renameByModel, findDefinition(req));
}

void renameByModel(findDefinition(RenameRequest req), TModel tm, RenameSolver solver) {
    println("Finding definition in TModel \'<tm.modelName>\'");

    loc fileUnderCursor = req.cursor[0].src.top;
    loc def = getDefLocation(tm, req.cursor);
    IdRole defRole = tm.definitions[def].idRole;

    // Rename occurrences in this file
    solver.collectTModel(fileUnderCursor, renameByModel, rename(defRole, def, req.newName));

    // Rename occurrences in any other files, if the renaming is not local
    // if (!isLocalRename(tm, def)) {
    //     for (loc m <- possibleDownstreamUsers(solver, req.workspaceFolders, def), m != fileUnderCursor) {
    //         solver.collectParseTree(m, renameByTree, rename(defRole, def, req.newName));
    //     }
    // }
}

void renameByModel(rename(role:variableId(), loc def, str newName), TModel tm, RenameSolver solver) {
    println("Renaming <role> occurrences in TModel \'<tm.modelName>\'");

    // Register edit for uses of def in this file
    for (loc u <- invert(tm.useDef)[def]) {
        solver.textEdit(replace(u, newName));
    }

    // Register edit for definitions in this file
    if (tm.definitions[def]? && tm.definitions[def].idRole == role) {
        solver.textEdit(replace(def, newName));
    }
}

default void renameByModel(RenameState state, TModel _, RenameSolver _) {
    throw "`renameByModel` not implemented for `<state>`";
}

// void renameByTree(downstreamUsers(l, newName), Tree m, RenameSolver solver) {
//     println("Processing tree \'<m.src>\'");
//     // If newName exists in parse tree, call collectTModel
//     // Else, do nothing
// }

// default void renameByTree(RenameState state, Tree _, RenameSolver _) {
//     throw "`renameByTree` not implemented for `<state>`";
// }


bool isValidName(str name) {
    try {
        parse(#Id, name);
        return true;
    } catch ParseError(_): {
        return false;
    }
}

loc getDefLocation(TModel tm, list[Tree] focus) {
    for (Tree t <- focus) {
        if (tm.definitions[t.src]?) {
            return tm.definitions[t.src].defined;
        }
    }

    throw "No definition for any cursor!";
}

// bool isLocalRename(TModel tm, loc def) {
//     // TODO Optimize
//     return false;
// }

// set[loc] possibleDownstreamUsers(RenameSolver solver, set[loc] workspaceFolders, loc def) {
//     set[loc] possibleUsers = {};
//     for (loc wsFolder <- workspaceFolders) {
//         for (loc picoFile <- find(wsFolder, "pico")) {
//             possibleUsers += picoFile;
//         }
//     }
//     return possibleUsers;
// }
