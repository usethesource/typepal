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
module examples::pico::RenameTest

import examples::pico::Rename;
import examples::pico::Syntax;

import analysis::typepal::refactor::TextEdits;

import util::LanguageServer; // computeFocusList

import IO;
import List;
import Message;
import ParseTree;
import Set;
import String;
import util::FileSystem;

tuple[list[DocumentEdit] edits, set[Message] msgs] basicRename(str newName = "foo", int line = 2, int col = 17) {
    prog = parse(#start[Program], |lib://typepal/src/examples/pico/fac.pico|);
    cursor = computeFocusList(prog, line, col);
    return renamePico(cursor, newName);
}

test bool doesNotCrash() {
    <edits, _> = basicRename();
    return true;
}

test bool hasFiveChanges() {
    <edits, _> = basicRename();
    return size(edits) == 1 && size(edits[0].edits) == 5;
}

test bool editsHaveLangthOfNameUnderCursor() {
    <edits, _> = basicRename();
    for (changed(_, rs) <- edits, replace(loc l, _) <- rs) {
        if (size("output") != l.length) return false;
    }
    return true;
}

test bool failsWithError() {
    if (<_, {error(_, _), *_}> := basicRename(col = 26)) {
        return true;
    }
    return false;
}

test bool invalidName() {
    if (<_, {error(_, _), *_}> := basicRename(newName = "_foo")) {
        return true;
    }
    return false;
}
