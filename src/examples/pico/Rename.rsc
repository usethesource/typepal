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

import examples::pico::Syntax;

extend analysis::typepal::refactor::Rename;

data Tree;


alias RenameRequest = tuple[list[Tree] cursorFocus, str newName];

data RenameState
    = initialRequest(RenameRequest r)
    | downstreamUsers(loc l, str newName)
    ;

void initSolver(RenameSolver solver, RenameConfig config, <list[Tree] cursorFocus, str newName>) {
    if (!isValidName(newName)) {
        // gooi errors
        solver.message(error("Not a valid name!"));
        return;
    }

    loc currentModule = cursorFocus[0].src.top;
    solver.collectTModel(currentModule, collect, initialRequest(<cursorFocus, newName>));
}

void collect(initialRequest(<cursorFocus, newName>), TModel tm, RenameSolver solver) {
    loc def = getDefLocation(tm, cursorFocus);
    if (!isLocalRename(tm, def)) {
        for (loc m <- possibleDownstreamUsers(solver, def)) {
            solver.collectParseTree(m, consider, downstreamUsers(def, newName));
        }
    }

    collect(downstreamUsers(def, newName), tm, solver);
}

void collect(downstreamUsers(l, newName), TModel tm, RenameSolver solver) {
    // Register edits and
}

default void collect(RenameState state, TModel _, RenameSolver _) {
    throw "`collect` not implemented for `<state>`";
}

void consider(downstreamUsers(l, newName), Tree m, RenameSolver solver) {
    // If newName exists in parse tree, call collectTModel
    // Else, do nothing
}

default void consider(RenameState state, Tree _, RenameSolver _) {
    throw "`consider` not implemented for `<state>`";
}


bool isValidName(str name);
loc getDefLocation(TModel tm, list[Tree] focus);
bool isLocalRename(TModel tm, loc def);
set[loc] possibleDownstreamUsers(RenameSolver solver, loc def);
