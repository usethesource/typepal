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
@bootstrapParser
module analysis::typepal::refactor::Rename

extend analysis::typepal::refactor::TextEdits;

extend Message;
import util::Reflective;

import IO;
import List;

data TModel;
data Tree;

data RenameState;

alias RenameResult = tuple[list[DocumentEdit], map[str, ChangeAnnotation], set[Message]];

data RenameSolver(
        RenameResult() run = RenameResult() { fail; }
      , void(loc l, void(RenameState, Tree, RenameSolver) doWork, RenameState state) collectParseTree = void(loc _, void(RenameState, Tree, RenameSolver) _, RenameState _) { throw "Not implemented!"; }
      , void(loc l, void(RenameState, TModel, RenameSolver) doWork, RenameState state) collectTModel = void(loc _, void(RenameState, TModel, RenameSolver) _, RenameState _) { throw "Not implemented!"; }
      , void(Message) msg = void(Message _) { fail; }
      , void(DocumentEdit) documentEdit = void(DocumentEdit _) { fail; }
      , void(TextEdit) textEdit = void(TextEdit _) { fail; }
      , void(str, ChangeAnnotation) annotation = void(str _, ChangeAnnotation _) { fail; }
      , value(str) readStore = value(str _) { fail; }
      , void(str, value) writeStore = void(str _, value _) { fail; }
) = rsolver();

data RenameConfig
    = rconfig(
        Tree(loc) parseLoc
      , TModel(loc) tmodelForLoc
    );

alias TreeTask = tuple[loc file, void(RenameState, Tree, RenameSolver) work, RenameState state];
alias ModelTask = tuple[loc file, void(RenameState, TModel, RenameSolver) work, RenameState state];

@example{
    Consumer implements something like:
    ```
    alias RenameRequest = tuple[list[Tree] cursorFocus, str newName];

    public tuple[list[DocumentEdit], map[str, ChangeAnnotation], set[Message] msgs] rename(RenameRequest request) {
        RenameConfig config = rconfig(parseFunc, typeCheckFunc);
        RenameSolver solver = newSolverForConfig(config);
        initSolver(solver, config, request);
        return solver.run();
    }
    ```
}
RenameSolver newSolverForConfig(RenameConfig config) {
    RenameSolver solver = rsolver();
    // COLLECT
    list[TreeTask] treeTasks = [];
    solver.collectParseTree = void(loc l, void(RenameState, Tree, RenameSolver) doWork, RenameState state) {
        treeTasks += <l, doWork, state>;
    };

    list[ModelTask] modelTasks = [];
    solver.collectTModel = void(loc l, void(RenameState, TModel, RenameSolver) doWork, RenameState state) {
        modelTasks += <l, doWork, state>;
    };

    // REGISTER
    set[Message] messages = {};
    solver.msg = void(Message msg) {
        messages += msg;
    };

    lrel[loc file, DocumentEdit edit] docEdits = [];
    solver.documentEdit = void(DocumentEdit edit) {
        loc f = edit has file ? edit.file : edit.from;
        docEdits += <f, edit>;
    };

    solver.textEdit = void(TextEdit edit) {
        loc f = edit.range.top;
        docEdits += <f, changed(f, [edit])>;
    };

    map[str id, ChangeAnnotation annotation] annotations = ();
    solver.annotation = void(str annotationId, ChangeAnnotation annotation) {
        if (annotationId in annotations) throw "An annotation with id \'<annotationId>\' already exists!";
        annotations[annotationId] = annotation;
    };

    // STORE
    map[str, value] store = ();
    solver.readStore = value(str key) { return store[key]; };
    solver.writeStore = void(str key, value val) {
        store[key] = val;
    };

    // RUN
    solver.run = RenameResult() {
        solve(treeTasks, modelTasks) {
            // TODO Batch per file
            // TODO Cache (& invalidate!) results
            println("<size(treeTasks)> tree tasks remaining");
            while ([TreeTask tt, *remaining] := treeTasks) {
                treeTasks = remaining;
                Tree t = config.parseLoc(tt.file);
                tt.work(tt.state, t, solver);
            }

            println("<size(modelTasks)> model tasks remaining");
            while ([ModelTask mt, *remaining] := modelTasks) {
                modelTasks = remaining;
                TModel tm = config.tmodelForLoc(mt.file);
                mt.work(mt.state, tm, solver);
            }
        }

        // Merge document edits
        return <mergeTextEdits(docEdits.edit), annotations, messages>;
    };

    return solver;
}

list[DocumentEdit] mergeTextEdits(list[DocumentEdit] edits) {
    // Only merge subqequent text edits to the same file.
    // Leave all other edits in the order in which they were registered
    list[DocumentEdit] mergedEdits = [];
    loc runningFile = |unknown:///|;
    list[TextEdit] runningEdits = [];

    void batchRunningEdits(loc thisFile) {
        if (runningEdits != []) {
            mergedEdits += changed(runningFile, runningEdits);
        }
        runningFile = thisFile;
        runningEdits = [];
    }

    for (DocumentEdit e <- edits) {
        loc thisFile = e has file ? e.file : e.from;
        if (thisFile != runningFile) {
            batchRunningEdits(thisFile);
        }

        if (e is changed) {
            runningEdits += e.edits;
        } else {
            batchRunningEdits(thisFile);
            mergedEdits += e;
        }
    }

    batchRunningEdits(|unknown:///|);

    return mergedEdits;
}
