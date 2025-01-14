@license{
Copyright (c) 2018-2023, NWO-I CWI and Swat.engineering
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

import examples::pico::PicoSyntax;
extend examples::pico::PicoChecker;

extend analysis::typepal::refactor::Rename;

import Exception;
import IO;
import Relation;
import util::FileSystem;

data Tree;

alias RenameRequest = tuple[list[Tree] cursor, str newName, set[loc] workspaceFolders];

data RenameState
    = initialRequest(RenameRequest r)
    | downstreamUsers(loc l, str newName)
    ;

@memo{expireAfter(minutes=1), maximumSize(50)}
Tree parseLoc(loc l) {
    return parse(#start[Program], l);
}

@memo{expireAfter(minutes=1), maximumSize(50)}
TModel tmodelForLoc(loc l) {
    return collectAndSolve(parseLoc(l));
}

public tuple[list[DocumentEdit] edits, map[str, ChangeAnnotation] annos, set[Message] msgs] rename(RenameRequest request) {
    RenameConfig config = rconfig(parseLoc, tmodelForLoc);

    RenameSolver solver = newSolverForConfig(config);
    initSolver(solver, config, request);
    return solver.run();
}

void initSolver(RenameSolver solver, RenameConfig config, RenameRequest req) {
    if (!isValidName(req.newName)) {
        // gooi errors
        solver.msg(error("Not a valid name: \'<req.newName>\'!"));
        return;
    }

    loc currentModule = req.cursor[0].src.top;
    solver.collectTModel(currentModule, renameByModel, initialRequest(req));
}

void renameByModel(initialRequest(RenameRequest req), TModel tm, RenameSolver solver) {
    println("Processing TModel \'<tm.modelName>\'");

    loc def = getDefLocation(tm, req.cursor);

    // Register edit for definition name
    solver.textEdit(replace(def, req.newName));

    if (!isLocalRename(tm, def)) {
        for (loc m <- possibleDownstreamUsers(solver, req.workspaceFolders, def)) {
            solver.collectParseTree(m, renameByTree, downstreamUsers(def, req.newName));
        }
    }

    renameByModel(downstreamUsers(def, req.newName), tm, solver);
}

void renameByModel(downstreamUsers(def, newName), TModel tm, RenameSolver solver) {
    println("Processing TModel \'<tm.modelName>\'");

    for (loc u <- invert(tm.useDef)[def]) {
        // Register edit for use
        solver.textEdit(replace(u, newName));
    }
}

default void renameByModel(RenameState state, TModel _, RenameSolver _) {
    throw "`renameByModel` not implemented for `<state>`";
}

void renameByTree(downstreamUsers(l, newName), Tree m, RenameSolver solver) {
    println("Processing tree \'<m.src>\'");
    // If newName exists in parse tree, call collectTModel
    // Else, do nothing
}

default void renameByTree(RenameState state, Tree _, RenameSolver _) {
    throw "`renameByTree` not implemented for `<state>`";
}


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

bool isLocalRename(TModel tm, loc def) {
    // TODO Optimize
    return false;
}

set[loc] possibleDownstreamUsers(RenameSolver solver, set[loc] workspaceFolders, loc def) {
    set[loc] possibleUsers = {};
    for (loc wsFolder <- workspaceFolders) {
        for (loc picoFile <- find(wsFolder, "pico")) {
            possibleUsers += picoFile;
        }
    }
    return possibleUsers;
}
