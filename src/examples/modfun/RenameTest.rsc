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
module examples::modfun::RenameTest

import examples::modfun::Rename;
import examples::modfun::Syntax;

import analysis::diff::edits::TextEdits;

import examples::rename::Focus;
import IO;
import List;
import ParseTree;
import Set;
import String;
import util::FileSystem;

tuple[list[DocumentEdit] edits, set[Message] msgs] basicRename(str modName, int line, int col, str newName = "foo") {
    prog = parse(#start[ModFun], |project://typepal/src/examples/modfun/<modName>.mfun|);
    cursor = computeFocusList(prog, line, col);
    return renameModules(cursor, newName);
}

list[int] sortedEditAmounts(list[DocumentEdit] edits) =
    sort([size(e.edits) | e <- edits]);

void checkNoErrors(set[Message] msgs) {
    if (m <- msgs, m is error) {
        throw "Renaming threw errors:\n - <intercalate("\n - ", toList(msgs))>";
    }
}

test bool duplicateModuleName() {
    <edits, msgs> = basicRename("A", 1, 8, newName = "B");
    return size({m | m <- msgs, m is error}) >= 1;
}

test bool moduleName() {
    <edits, msgs> = basicRename("A", 1, 8, newName = "C");

    checkNoErrors(msgs);
    return size(edits) == 2
        && sortedEditAmounts(edits) == [1, 1];
}

test bool overloadedFunc() {
    <edits, msgs> = basicRename("A", 3, 9);

    checkNoErrors(msgs);
    return size(edits) == 2
        && sortedEditAmounts(edits) == [1, 2];
}

test bool importedFunc() {
    <edits, msgs> = basicRename("B", 3, 19);

    checkNoErrors(msgs);
    return size(edits) == 2
        && sortedEditAmounts(edits) == [1, 2];
}
