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

import analysis::typepal::refactor::TextEdits;

extend Message;
import ParseTree;
import util::Reflective;

data TModel;
data RenameState;


data RenameSolver
    = solver(
      void(loc l, void(RenameState, Tree, RenameSolver) doWork, RenameState state) collectParseTree
    , void(loc l, void(RenameState, TModel, RenameSolver) doWork, RenameState state) collectTModel
    , void(Message) message
    , void(set[Message]) messages
    , void(DocumentEdit) documentEdit
    , void(TextEdit) textEdit
    , void(ChangeAnnotation) annotation
    , value(str) readStore
    , void(str, value) writeStore
);



data RenameConfig
    = rconfig(
        Tree(loc) parseLocs
      , TModel(loc) tmodelForLocs
    )
    ;

@example{
    Consumer implements something like:
    ```
    alias RenameRequest = tuple[list[Tree] cursorFocus, str newName];

    public tuple[list[DocumentEdit], map[str, ChangeAnnotation], set[Message] msgs] rename(
        RenameConfig config
      , RenameRequest request
      , void(RenameSolver, RenameConfig, RenameRequest) initSolver // pre-check
    ) {
        RenameSolver solver = newSolverForConfig(config);
        initSolver(solver, config, request);
        return solver.run();
    }
    ```
}
RenameSolver newSolverForConfig(RenameConfig config) {
    fail;
}
