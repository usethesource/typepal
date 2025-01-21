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

module examples::modules::Rename

import examples::modules::Checker;
import examples::modules::Syntax;

import analysis::typepal::refactor::Rename;
import analysis::typepal::refactor::TextEdits;

import Exception;
import IO;
import Map;
import Relation;
import Set;
import util::FileSystem;
import util::Maybe;

data RenameConfig(
    set[loc] workspaceFolders = {}
);

public tuple[list[DocumentEdit] edits, map[str, ChangeAnnotation] annos, set[Message] msgs] renameModules(list[Tree] cursor, str newName, set[loc] workspaceFolders) {
    bool nameIsValid = any(ModuleId _ <- cursor)
        ? isValidName(moduleId(), newName)
        : isValidName(structId(), newName);

    if (!nameIsValid) {
        return <[], (), {error("Invalid name: <newName>", cursor[0].src)}>;
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
        , skipCandidate = skipCandidate
        , workspaceFolders = workspaceFolders
      )
    );
}

tuple[set[Define], set[loc]] findCandidates(list[Tree] cursor, Tree(loc) getTree, TModel(Tree) getTModel, Renamer r) {
    str cursorName = "<cursor[0]>";

    set[Define] defs = {};
    set[loc] uses = {};

    for (loc wsFolder <- r.getConfig().workspaceFolders
       , loc f <- find(wsFolder, "modules")) {
        Tree t = getTree(f);

        Maybe[TModel] tmCache = nothing();
        TModel getLocalTModel() {
            if (tmCache is nothing) {
                tmCache = just(getTModel(t));
            }
            return tmCache.val;
        }

        visit (t) {
            case (Import) `import <ModuleId id>`: {
                if ("<id>" == cursorName) {
                    uses += id.src;
                }
            }
            case (DeclInStruct) `<Type ty>`: {
                if ("<ty>" == cursorName) {
                    uses += ty.src;
                }
            }
            case s:(TopLevelDecl) `struct <Id id> { <DeclInStruct* _> }`: {
                if ("<id>" == cursorName
                 && tm := getLocalTModel()
                 && Define d:<_, _, _, structId(), _, _> := tm.definitions[s.src]) {
                    defs += d;
                }
            }
            case m:(Program) `module <ModuleId id> <Import* _> <TopLevelDecl* _>`: {
                if ("<id>" == cursorName
                 && tm := getLocalTModel()
                 && Define d:<_, _, _, moduleId(), _, _> := tm.definitions[m.src]) {
                    defs += d;
                }
            }
        }
    }
    return <defs, uses>;
}

bool tryParse(type[&T <: Tree] tp, str s) {
    try {
        parse(tp, s);
        return true;
    } catch ParseError(_): {
        return false;
    }
}

bool isValidName(moduleId(), str name) = tryParse(#ModuleId, name);
bool isValidName(structId(), str name) = tryParse(#Id, name);

bool skipCandidate(set[Define] defs, Tree modTree, Renamer _) {
    // Only if the name of the definition appears in the module, consider it a rename candidate
    set[str] names = {d.id | d <- defs};
    return !(any(/Id t := modTree, "<t>" in names)
          || any(/ModuleId t := modTree, "<t>" in names));
}

void renameDef(Define def, str newName, TModel tm, Renamer r) {
    if (def in tm.defines) {
        r.textEdit(replace(def.defined, newName));
    }
}

void renameUses(Define _, str newName, set[loc] useCandidates, TModel _, Renamer r) {
    for (loc u <- useCandidates) {
        r.textEdit(replace(u, newName));
    }
}
