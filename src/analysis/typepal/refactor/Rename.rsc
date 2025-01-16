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
@bootstrapParser
module analysis::typepal::refactor::Rename

import analysis::typepal::refactor::TextEdits;

import analysis::typepal::TModel;


import IO;
import List;
import Map;
import Message;
import Node;
import ParseTree;
import Set;

import util::Reflective;

alias RenameResult = tuple[list[DocumentEdit], map[str, ChangeAnnotation], set[Message]];

data Renamer
    = renamer(
        void(Message) msg
      , void(DocumentEdit) documentEdit
      , void(TextEdit) textEdit
      , void(str, ChangeAnnotation) annotation
      , value(str) readStore
      , void(str, value) writeStore
    );

RenameResult rename(
        list[Tree] cursor
      , str newName
      , Tree(loc) parseLoc
      , TModel(Tree) tmodelForTree
      , set[Define](list[Tree] cursor, TModel(Tree) getTModel, Renamer r) findDefinitions
      , set[loc](set[Define] defs, Renamer r) findCandidateFiles
      , void(Define def, str newName, TModel tm, Renamer r) renameDef
      , bool(set[Define] defs, Tree t, Renamer r) skipCandidate = bool(_, _, _) { return false; }
      , bool debug = true) {

    // Tree & TModel caching

    @memo{maximumSize(50)}
    TModel getTModelCached(Tree t) = tmodelForTree(t);

    @memo{maximumSize(50)}
    Tree parseLocCached(loc l) {
        // We already have the parse tree of the module under cursor
        if (l == cursor[-1].src.top) {
            return cursor[-1];
        }

        return parseLoc(l);
    }

    // Messages
    set[Message] messages = {};
    void registerMessage(Message msg) {
        messages += msg;
    };

    // Edits
    set[value] editsSeen = {};
    list[DocumentEdit] docEdits = [];

    void checkEdit(te:replace(loc range, _)) {
        if (te in editsSeen) {
            messages += error("Multiple replace edits for this location.", range);
        }

        loc f = range.top;
        for (changed(f, _) <- editsSeen) {
            messages += error("Multiple replace edits for this location.", range);
        }
    }

    void checkEdit(DocumentEdit e) {
        if (changed(f, tes) := e) {
            // Check contents of DocumentEdit
            for (te:replace(range, _) <- tes) {
                // Check integrity
                if (range.top != f) {
                    messages += error("Invalid replace edit for this location. This location is not in <f>, for which it was registered.", range);
                }

                // Check text edits
                checkEdit(te);
            }
        } else if (e in editsSeen) {
            loc file = e has file ? e.file : e.from;
            messages += error("Multiple <getName(e)> edits for this file.", file);
        }
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

    map[str id, ChangeAnnotation annotation] annotations = ();
    void registerAnnotation(str annotationId, ChangeAnnotation annotation) {
        if (annotationId in annotations) throw "An annotation with id \'<annotationId>\' already exists!";
        annotations[annotationId] = annotation;
    };

    // Store
    map[str, value] store = ();
    value readStore(str key) { return store[key]; };
    void writeStore(str key, value val) { store[key] = val; };

    Renamer r = renamer(
        registerMessage
      , registerDocumentEdit
      , registerTextEdit
      , registerAnnotation
      , readStore
      , writeStore
    );

    if (debug) println("Renaming <cursor[0].src> to \'<newName>\'");

    if (debug) println("+ Finding definitions for cursor at <cursor[0].src>");
    set[Define] defs = findDefinitions(cursor, getTModelCached, r);
    if (debug) println("+ Finding candidate files");
    set[loc] candidates = findCandidateFiles(defs, r);
    for (loc f <- candidates) {
        if (debug) println("  - Processing candidate <f>");
        if (debug) println("    + Retrieving parse tree");
        Tree t = parseLocCached(f);
        if (skipCandidate(defs, t, r)) {
            if (debug) println("    + Skipping");
            continue;
        }

        if (debug) println("    + Retrieving TModel");
        TModel tm = getTModelCached(t);
        if (debug) println("    + Renaming each definition");
        for (Define d <- defs) {
            if (debug) println("      - Renaming <d.idRole> \'<d.id>\'");
            renameDef(d, newName, tm, r);
        }
        if (debug) println("  - Done!");
    }
    if (debug) println("+ Done!");
    if (debug) {
        println("\n\n============\nRename statistics\n============\n");
        int nDocs = size({f | de <- docEdits, f := (de has file ? de.file : de.from)});
        int nEdits = (0 | it + ((changed(_, tes) := e) ? size(tes) : 1) | e <- docEdits);

        int nErrors = size({msg | msg <- messages, msg is error});
        int nWarnings = size({msg | msg <- messages, msg is warning});
        int nInfos = size({msg | msg <- messages, msg is info});

        println(" # of documents affected: <nDocs>");
        println(" # of text edits:         <nEdits>");
        println(" # of messages:           <size(messages)>");
        println("   (<nErrors> errors, <nWarnings> warnings and <nInfos> infos)");
        println(" # of annotations:        <size(annotations)>");
    }

    return <docEdits, annotations, messages>;
}
