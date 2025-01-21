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
import examples::pico::Checker;

import analysis::typepal::TModel;

import analysis::typepal::refactor::Rename;
import analysis::typepal::refactor::TextEdits;

import Exception;
import IO;
import Relation;
import util::FileSystem;

data Tree;

public tuple[list[DocumentEdit] edits, map[str, ChangeAnnotation] annos, set[Message] msgs] renamePico(list[Tree] cursor, str newName) {
    if (!isValidName(newName)) {
        return <[], (), {error("\'<newName>\' is not a valid name here.", cursor[0].src)}>;
    }

    return rename(
        cursor
      , newName
      , rconfig(
          Tree(loc l) { return parse(#start[Program], l); }
        , collectAndSolve
        , findCandidates
        , renameDef
        , renameUses
        , skipCandidate = bool(_, _, _) { return false; }
      )
    );
}

tuple[set[Define], set[loc]] findCandidates(list[Tree] cursor, Tree(loc) _, TModel(Tree) getTModel, Renamer _) {
    TModel tm = getTModel(cursor[-1]);
    if (Tree t <- cursor
      , tm.definitions[t.src]?) {
        set[Define] defs = {tm.definitions[t.src]};
        set[loc] uses = invert(tm.useDef)[defs.defined];
            return <defs, uses>;
    }

    return <{}, {}>;
}

void renameDef(Define def, str newName, TModel tm, Renamer r) {
    // Register edit for definitions in this file
    r.textEdit(replace(def.defined, newName));
}

void renameUses(set[Define] _, str newName, set[loc] candidates, TModel tm, Renamer r) {
    // Register edit for uses of def in this file
    for (loc u <- candidates) {
        r.textEdit(replace(u, newName));
    }
}

bool isValidName(str name) {
    try {
        parse(#Id, name);
        return true;
    } catch ParseError(_): {
        return false;
    }
}
