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
module analysis::typepal::refactor::Rename

import analysis::typepal::refactor::TextEdits;

import analysis::typepal::FailMessage;
import analysis::typepal::Messenger;
import analysis::typepal::TModel;


import IO;
import List;
import Map;
import Message;
import Node;
import ParseTree;
import Relation;
import Set;

alias RenameResult = tuple[list[DocumentEdit], set[Message]];

data Renamer
    = renamer(
        void(FailMessage) msg
      , void(DocumentEdit) documentEdit
      , void(TextEdit) textEdit
      , RenameConfig() getConfig

      // Helpers
      , void(str, loc) warning
      , void(str, loc) info
      , void(str, loc) error
    );

data RenameConfig
    = rconfig(
        Tree(loc) parseLoc
      , TModel(Tree) tmodelForTree
    );

RenameResult rename(
        list[Tree] cursor
      , str newName
      , RenameConfig config
      , bool debug = true) {

    // Tree & TModel caching

    @memo{maximumSize(50)}
    TModel getTModelCached(Tree t) = config.tmodelForTree(t);

    @memo{maximumSize(50)}
    Tree parseLocCached(loc l) {
        // We already have the parse tree of the module under cursor
        if (l == cursor[-1].src.top) {
            return cursor[-1];
        }

        return config.parseLoc(l);
    }

    // Make sure user uses cached functions
    cachedConfig = config[parseLoc = parseLocCached][tmodelForTree = getTModelCached];

    // Messages
    set[FailMessage] messages = {};
    bool errorReported() = messages != {} && any(m <- messages, m is error);
    void registerMessage(FailMessage msg) { messages += msg; };
    AType getType(Tree t) {
        TModel tm = getTModelCached(parseLocCached(t.src.top));
        if (tm.facts[t.src]?) {
            return tm.facts[t.src];
        }

        return tvar(|unknown:///|);
    }
    set[Message] getMessages() = {toMessage(m, getType) | m <- messages};

    // Edits
    set[loc] editsSeen = {};
    list[DocumentEdit] docEdits = [];

    void checkEdit(replace(loc range, _)) {
        if (range in editsSeen) {
            registerMessage(error(range, "Multiple replace edits for this location."));
        }
        editsSeen += range;
    }

    void checkEdit(DocumentEdit e) {
        loc file = e has file ? e.file : e.from;
        if (changed(f, tes) := e) {
            // Check contents of DocumentEdit
            for (te:replace(range, _) <- tes) {
                // Check integrity
                if (range.top != f) {
                    registerMessage(error(range, "Invalid replace edit for this location. This location is not in <f>, for which it was registered."));
                }

                // Check text edits
                checkEdit(te);
            }
        } else if (file in editsSeen) {
            registerMessage(error(file, "Multiple <getName(e)> edits for this file."));
        }

        editsSeen += file;
    }

    void registerDocumentEdit(DocumentEdit e) {
        checkEdit(e);
        docEdits += e;
    };

    void registerTextEdit(TextEdit e) {
        checkEdit(e);

        loc f = e.range.top;
        if ([*pre, changed(f, prev)] := docEdits) {
            // If possible, merge with latest document edit
            // TODO Just assign to docEdits[-1], once this issue has been solved:
            // https://github.com/usethesource/rascal/issues/2123
            docEdits = [*pre, changed(f, prev + e)];
        } else {
            // Else, create new document edit
            docEdits += changed(f, [e]);
        }
    };

    Renamer r = renamer(
        registerMessage
      , registerDocumentEdit
      , registerTextEdit
      , RenameConfig() { return cachedConfig; }
      , void(str s, value at) { registerMessage(info(at, s)); }
      , void(str s, value at) { registerMessage(warning(at, s)); }
      , void(str s, value at) { registerMessage(error(at, s)); }
    );

    if (debug) println("Renaming <cursor[0].src> to \'<newName>\'");

    if (debug) println("+ Finding definitions for cursor at <cursor[0].src>");
    defs = getCursorDefinitions(cursor, parseLocCached, getTModelCached, r);

    if (defs == {}) r.error("No definitions found", cursor[0].src);
    if (errorReported()) return <docEdits, getMessages()>;

    if (debug) println("+ Finding occurrences of cursor");
    <maybeDefFiles, maybeUseFiles> = findOccurrenceFiles(defs, cursor, parseLocCached, r);

    if (maybeDefFiles != {}) {
        if (debug) println("+ Finding additional definitions");
        set[Define] additionalDefs = {};
        for (loc f <- maybeDefFiles) {
            if (debug) println("  - ... in <f>");
            tr = parseLocCached(f);
            tm = getTModelCached(tr);
            additionalDefs += findAdditionalDefinitions(defs, tr, tm);
        }
        defs += additionalDefs;
    }

    defFiles = {d.defined.top | d <- defs};

    if (debug) println("+ Renaming definitions across <size(defFiles)> files");
    for (loc f <- defFiles) {
        fileDefs = {d | d <- defs, d.defined.top == f};
        if (debug) println("  - ... <size(fileDefs)> in <f>");

        tr = parseLocCached(f);
        tm = getTModelCached(tr);

        for (d <- defs, d.defined.top == f) {
            renameDefinition(d, newName, tm, r);
        }
    }

    if (debug) println("+ Renaming uses across <size(maybeUseFiles)> files");
    for (loc f <- maybeUseFiles) {
        if (debug) println("  - ... in <f>");

        tr = parseLocCached(f);
        tm = getTModelCached(tr);

        renameUses(defs, newName, tm, r);
    }

    set[Message] convertedMessages = getMessages();

    if (debug) println("+ Done!");
    if (debug) {
        println("\n\n=================\nRename statistics\n=================\n");
        int nDocs = size({f | de <- docEdits, f := (de has file ? de.file : de.from)});
        int nEdits = (0 | it + ((changed(_, tes) := e) ? size(tes) : 1) | e <- docEdits);

        int nErrors = size({msg | msg <- convertedMessages, msg is error});
        int nWarnings = size({msg | msg <- convertedMessages, msg is warning});
        int nInfos = size({msg | msg <- convertedMessages, msg is info});

        println(" # of documents affected: <nDocs>");
        println(" # of text edits:         <nEdits>");
        println(" # of messages:           <size(convertedMessages)>");
        println("   (<nErrors> errors, <nWarnings> warnings and <nInfos> infos)");

        if (size(convertedMessages) > 0) {
            println("\n===============\nMessages\n===============");
            for (msg <- convertedMessages) {
                println(" ** <msg>");
            }
            println();
        }
    }

    return <docEdits, convertedMessages>;
}

default set[Define] getCursorDefinitions(list[Tree] cursor, Tree(loc) _, TModel(Tree) getModel, Renamer r) {
    loc cursorLoc = cursor[0].src;
    TModel tm = getModel(cursor[-1]);
    for (Tree c <- cursor) {
        if (tm.definitions[c.src]?) {
            return {tm.definitions[c.src]};
        } else if (defs: {_, *_} := tm.useDef[c.src]) {
            if (any(d <- defs, d.top != cursorLoc.top)) {
                r.error("Rename not implemented for cross-file definitions. Please overload `getCursorDefinitions`.", cursorLoc);
                return {};
            }

            return {tm.definitions[d] | d <- defs, tm.definitions[d]?};
        }
    }

    r.error("Could not find definition to rename.", cursorLoc);
    return {};
}

default tuple[set[loc] defFiles, set[loc] useFiles] findOccurrenceFiles(set[Define] cursorDefs, list[Tree] cursor, Tree(loc) _, Renamer r) {
    loc f = cursor[0].src.top;
    if (any(d <- cursorDefs, f != d.defined.top)) {
        r.error("Rename not implemented for cross-file definitions. Please overload `findOccurrenceFiles`.", cursor[0].src);
        return <{}, {}>;
    }

    return <{f}, {f}>;
}

default set[Define] findAdditionalDefinitions(set[Define] cursorDefs, Tree tr, TModel tm) = {};

default void renameDefinition(Define d, str newName, TModel tm, Renamer r) {
    r.textEdit(replace(d.defined, newName));
}

default void renameUses(set[Define] defs, str newName, TModel tm, Renamer r) {
    for (loc u <- invert(tm.useDef)[defs.defined]) {
        r.textEdit(replace(u, newName));
    }
}