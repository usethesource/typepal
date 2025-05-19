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

import analysis::diff::edits::TextEdits;
import analysis::typepal::FailMessage;
import analysis::typepal::Messenger;
import analysis::typepal::TModel;

import util::Monitor;

import Exception;
import IO;
import List;
import Map;
import Message;
import Node;
import ParseTree;
import Relation;
import Set;

alias RenameResult = tuple[list[DocumentEdit], set[Message]];
alias Focus = list[Tree];

// This leaves some room for more fine-grained steps should the user want to monitor that
private int WORKSPACE_WORK = 10;
private int FILE_WORK = 5;

@synopsis{Tracks state of renaming and provides halper functions.}
@description{
Tracks the state of the renaming, as an argument to every function of the rename framework.

* `msg` registers a ((FailMessage)). Registration of an ((error)) triggers premature termination of the renaming at the soonest possibility (typically before the next rename phase).
* `documentEdit` registers a ((DocumentEdit)), which represents a change required for the renaming.
* `textEdit` registers a ((TextEdit)), which represents a change required for the renaming. It is a convenience function that converts to a ((DocumentEdit)) internally, grouping ((TextEdit))s to the same file where possible.
* `getConfig` retrieves the ((analysis::typepal::refactor::Rename::RenameConfig)).
}
data Renamer
    = renamer(
        void(FailMessage) msg
      , void(DocumentEdit) documentEdit
      , void(TextEdit) textEdit
      , RenameConfig() getConfig
    );

@synopsis{Language-specific configuration of identifier renaming.}
@description{
Configures the rename for a specific language, by giving the following mandatory arguments:
* `Tree parseLoc(loc l)`, which parses a file and returns a ((ParseTree::Tree)). Typically this would be `parse(#StartSymbol, l)`.
* `TModel tmodelForTree(Tree t)`, which type-checks a ((ParseTree::Tree)) and returns a ((TModel)). Typically, this would be ((collectAndSolve)).
The configuration also takes some optional arguments:
* `TModel tmodelForLoc(loc l)`, which type-checks a file given its `loc` instead of its parse tree. This can be useful when the file does not have to be parsed to produce a ((TModel)), for example when it had already been type-checked just before starting the renaming. Defaults to `tmodelForTree(parseLoc(l))`.
* `bool debug`, which indicates whether debug output should be printed during the renaming. Defaults to `false`.
*`str jobLabel`, which can be used to change the base label of the rename progress bar. Defaults to `"Renaming"`.
}
data RenameConfig
    = rconfig(
        Tree(loc) parseLoc
      , TModel(Tree) tmodelForTree
      , TModel(loc) tmodelForLoc = TModel(loc l) { return tmodelForTree(parseLoc(l)); }
      , bool debug = false
      , str jobLabel = "Renaming"
    );

@synopsis{Sorts ((analysis::diff::edits::TextEdits::DocumentEdit))s.}
@description{
Applying edits through ((analysis::diff::edits::ExecuteTextEdits)) should happen in a specific order.
Specifically, files should be created before they can be modified, and after renaming them, modifications/deletions should refer to the new name.
This functions sorts edits in the following order.

1. ((analysis::diff::edits::TextEdits::created))
2. ((analysis::diff::edits::TextEdits::changed))
3. ((analysis::diff::edits::TextEdits::renamed))
4. ((analysis::diff::edits::TextEdits::removed))
}
list[DocumentEdit] sortDocEdits(list[DocumentEdit] edits) = sort(edits, bool(DocumentEdit e1, DocumentEdit e2) {
    if (e1 is created && !(e2 is created)) return true;
    if (e1 is changed && !(e2 is changed)) return !(e2 is created);
    if (e1 is renamed && !(e2 is renamed)) return (e2 is removed);
    return false;
});

@synopsis{Renames the identifier under the cursor to `newName` and returns the required ((analysis::diff::edits::TextEdits::DocumentEdit))s and ((Message::Message))s.}
@description{
Renames the identifier under the cursor (represented as a ((Focus))) to `newName`, given a specific ((analysis::typepal::refactor::Rename::RenameConfig)).
This renaming uses ((TModel))s produced by the type-checker.

The rename framework provides a default implementation, which can be selectively extended for languages that require different rename behaviour than the default. These functions constitute the implementation of renaming:
* ((analysis::typepal::refactor::Rename::getCursorDefinitions))
* ((analysis::typepal::refactor::Rename::findOccurrenceFiles))
* ((analysis::typepal::refactor::Rename::findAdditionalDefinitions))
* ((analysis::typepal::refactor::Rename::validateNewNameOccurrences))
* ((analysis::typepal::refactor::Rename::renameDefinition))
* ((analysis::typepal::refactor::Rename::renameUses))
* ((analysis::typepal::refactor::Rename::nameLocation))
}
@pitfalls{
* Since the ((analysis::typepal::refactor::Rename::RenameConfig)) that this function passes to the various hooks contains state and caches, it should never escape the scope of a single invoation of ((rename)). Instead, it should always be accessed via ((renamer))'s `getConfig`.
* The renaming highly depends on a type-check function `TModel(Tree)`. If such a function does not exist, this framework cannot function.
}
RenameResult rename(
        Focus cursor
      , str newName
      , RenameConfig config) {

    jobStart(config.jobLabel, totalWork = 2 * WORKSPACE_WORK + 1);
    jobStep(config.jobLabel, "Initializing renaming");

    // Tree & TModel caching

    @memo{maximumSize(50)}
    TModel getTModelCached(Tree t) {
        tm = config.tmodelForTree(t);
        if (msg <- tm.messages, msg is error) registerMessage(error(t.src.top, "Renaming failed, since this file has type error(s)."));
        return tm;
    }

    @memo{maximumSize(50)}
    TModel getTModelForLocCached(loc l) = config.tmodelForLoc(l);

    @memo{maximumSize(50)}
    Tree parseLocCached(loc l) {
        // We already have the parse tree of the module under cursor
        if (l == cursor[-1].src.top) {
            return cursor[-1];
        }

        try {
            return config.parseLoc(l);
        } catch ParseError(_): {
            registerMessage(error(l, "Renaming failed, since an error occurred while parsing this file."));
            return char(-1);
        }
    }

    // Make sure user uses cached functions
    cachedConfig = config
        [parseLoc = parseLocCached]
        [tmodelForTree = getTModelCached]
        [tmodelForLoc = getTModelForLocCached]
        ;

    // Messages
    set[FailMessage] messages = {};
    bool errorReported() = messages != {} && any(m <- messages, m is fm_error);
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
        if ([*pre, c:changed(f, _)] := docEdits) {
            // If possible, merge with latest document edit
            // TODO Just assign to docEdits[-1], once this issue has been solved:
            // https://github.com/usethesource/rascal/issues/2123
            docEdits = [*pre, c[edits = c.edits + e]];
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
    );

    jobStep(config.jobLabel, "Resolving definitions of <cursor[0].src>", work = WORKSPACE_WORK);
    defs = getCursorDefinitions(cursor, parseLocCached, getTModelCached, r);

    if (defs == {}) r.msg(error(cursor[0].src, "No definitions found"));
    if (errorReported()) {
        jobEnd(config.jobLabel, success=false);
        return <sortDocEdits(docEdits), getMessages()>;
    }

    jobStep(config.jobLabel, "Looking for files with occurrences of name under cursor", work = WORKSPACE_WORK);
    <maybeDefFiles, maybeUseFiles, newNameFiles> = findOccurrenceFiles(defs, cursor, newName, parseLocCached, r);

    jobTodo(config.jobLabel, work = (size(maybeDefFiles) + size(maybeUseFiles) + size(newNameFiles)) * FILE_WORK);

    set[Define] additionalDefs = {};
    solve (additionalDefs) {
        for (loc f <- maybeDefFiles) {
            jobStep(config.jobLabel, "Looking for additional definitions in <f>", work = 0);
            tr = parseLocCached(f);
            tm = getTModelCached(tr);
            additionalDefs += findAdditionalDefinitions(defs, tr, tm, r);
        }
        defs += additionalDefs;
    }
    jobStep(config.jobLabel, "Done looking for additional definitions", work = FILE_WORK * size(maybeDefFiles));

    for (loc f <- newNameFiles) {
        jobStep(config.jobLabel, "Validating occurrences of new name \'<newName>\' in <f>", work = FILE_WORK);
        tr = parseLocCached(f);
        validateNewNameOccurrences(defs, newName, tr, r);
    }
    if (errorReported()) {
        jobEnd(config.jobLabel, success = false);
        return <sortDocEdits(docEdits), getMessages()>;
    }

    defFiles = {d.defined.top | d <- defs};
    jobTodo(config.jobLabel, work = size(defFiles) * FILE_WORK);

    for (loc f <- defFiles) {
        fileDefs = {d | d <- defs, d.defined.top == f};
        jobStep(config.jobLabel, "Renaming <size(fileDefs)> definitions in <f>", work = FILE_WORK);
        tr = parseLocCached(f);
        tm = getTModelCached(tr);

        map[Define, loc] defNames = defNameLocations(tr, fileDefs, r);
        for (d <- fileDefs) {
            renameDefinition(d, defNames[d] ? d.defined, newName, tm, r);
        }
    }

    if (errorReported()) {
        jobEnd(config.jobLabel, success=false);
        return <sortDocEdits(docEdits), getMessages()>;
    }

    for (loc f <- maybeUseFiles) {
        jobStep(config.jobLabel, "Renaming uses in <f>", work = FILE_WORK);
        tr = parseLocCached(f);
        tm = getTModelCached(tr);

        renameUses(defs, newName, tm, r);
    }

    set[Message] convertedMessages = getMessages();

    if (config.debug) {
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

    jobEnd(config.jobLabel, success = !errorReported());
    return <sortDocEdits(docEdits), convertedMessages>;
}

// TODO If performance bottleneck, rewrite to binary search
@synopsis{Compute locations of names of `defs` in `tr`.}
private map[Define, loc] defNameLocations(Tree tr, set[Define] defs, Renamer _r) {
    map[loc, Define] definitions = (d.defined: d | d <- defs);
    set[loc] defsToDo = defs.defined;

    // If we have a single definition, we can put the pattern matcher to work
    if ({loc d} := defsToDo) {
        def = definitions[d];
        top-down visit (tr) {
            case t:appl(_, _):
                if (t@\loc?, d := t@\loc) {
                    return (def: nameLocation(t, def));
                }
        }
    }

    map[Define, loc] defNames = ();
    for (defsToDo != {}, /t:appl(_, _) := tr, t@\loc?, loc d := t@\loc, d in defsToDo) {
        def = definitions[d];
        defNames[def] = nameLocation(t, def);
        defsToDo -= d;
    }

    return defNames;
}

@synopsis{Computes ((Define))(s) for the name under `cursor` in ((ParseTree::Tree)) `_r`.}
default set[Define] getCursorDefinitions(Focus cursor, Tree(loc) _r, TModel(Tree) getModel, Renamer r) {
    loc cursorLoc = cursor[0].src;
    TModel tm = getModel(cursor[-1]);
    for (Tree c <- cursor) {
        if (tm.definitions[c.src]?) {
            return {tm.definitions[c.src]};
        } else if (defs: {_, *_} := tm.useDef[c.src]) {
            if (any(d <- defs, d.top != cursorLoc.top)) {
                r.msg(error(cursorLoc, "Rename not implemented for cross-file definitions. Please overload `getCursorDefinitions`."));
                return {};
            }

            return {tm.definitions[d] | d <- defs, tm.definitions[d]?};
        }
    }

    r.msg(error(cursorLoc, "Could not find definition to rename."));
    return {};
}

@synopsis{Computes in which files occurrences of `cursorDefs` and `newName` *might* occur (over-approximation). This is not supposed to call the type-checker on any file for performance reasons.}
@pitfalls{For any file in `defFiles + useFiles`, the framework calls `RenameConfig::tmodelForLoc`. If type-cehcking is expensive and this function over-approximates by a large margin, the performance of the renaming might degrade.}
default tuple[set[loc] defFiles, set[loc] useFiles, set[loc] newNameFiles] findOccurrenceFiles(set[Define] cursorDefs, Focus cursor, str newName, Tree(loc) _getTree, Renamer r) {
    loc f = cursor[0].src.top;
    if (any(d <- cursorDefs, f != d.defined.top)) {
        r.msg(error(cursor[0].src, "Rename not implemented for cross-file definitions. Please overload `findOccurrenceFiles`."));
        return <{}, {}, {}>;
    }

    return <{f}, {f}, any(/Tree t := f, "<t>" == newName) ? {f} : {}>;
}

@synopsis{Computes additional definitions (e.g. overloads of `cursorDefs`) in a single file.}
default set[Define] findAdditionalDefinitions(set[Define] _cursorDefs, Tree _tr, TModel _tm, Renamer _r) = {};

@synopsis{Validates for a single file with occurrences of `newName` that, when renaming all occurrences of `cursorDefs` to `newName`, no problems will be introduced.}
@examples{This could be used to detect many kinds of problems, e.g. static errors and semantic changes due to shadowing or overloading.}
default void validateNewNameOccurrences(set[Define] cursorDefs, str newName, Tree tr, Renamer r) {
    for (Define d <- cursorDefs) {
        r.msg(error(d.defined, "Renaming this to \'<newName>\' would clash with use of \'<newName>\' in <tr.src.top>."));
    }
}

@synopsis{Renames a single ((Define)) `_d `with its name at `nameLoc`, defined in ((TModel)) `_tm`, to `newName`, by producing corresponding ((DocumentEdit))s.}
default void renameDefinition(Define _d, loc nameLoc, str newName, TModel _tm, Renamer r) {
    r.textEdit(replace(nameLoc, newName));
}

@synopsis{{Renames all uses of `defs` in a single file/((TModel)) `tm`, by producing corresponding ((DocumentEdit))s.}}
default void renameUses(set[Define] defs, str newName, TModel tm, Renamer r) {
    for (loc u <- invert(tm.useDef)[defs.defined] - defs.defined) {
        r.textEdit(replace(u, newName));
    }
}

@synopsis{Finds the location of the identifier within definition ((ParseTree::Tree)) `t` corresponding to ((Define)) `d`, where `t.src == d.defined`.}
default loc nameLocation(Tree t, Define d) {
    // Try to find the first sub-tree that matches the name of the definition
    for (/Tree tr := t, tr@\loc?, "<tr>" == d.id) {
        return tr@\loc;
    }
    return t@\loc;
}
