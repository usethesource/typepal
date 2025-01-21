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

module examples::modfun::Rename

import examples::modfun::Checker;
import examples::modfun::Syntax;

import analysis::typepal::refactor::Rename;
import analysis::typepal::refactor::TextEdits;

import Exception;
import IO;
import List;
import Map;
import Relation;
import util::FileSystem;
import util::Maybe;

data RenameConfig(
    set[loc] workspaceFolders = {}
);

public tuple[list[DocumentEdit] edits, set[Message] msgs] renameModules(list[Tree] cursor, str newName, set[loc] workspaceFolders) {
    bool nameIsValid = any(ModId _ <- cursor)
        ? isValidName(moduleId(), newName)
        : isValidName(variableId(), newName);

    if (!nameIsValid) {
        return <[], {error("Invalid name: <newName>", cursor[0].src)}>;
    }

    return rename(
        cursor
      , newName
      , rconfig(
          Tree(loc l) { return parse(#start[ModFun], l); }
        , TModel(Tree pt) { return collectAndSolve(pt, config = tconfig(mayOverload = bool(set[loc] defs, map[loc, Define] defines) { return true; })); }
        , findCandidates
        , renameDef
        , renameUses
        , skipCandidate = skipCandidate
        , workspaceFolders = workspaceFolders
      )
    );
}

tuple[set[Define], set[loc]] findCandidates(list[Tree] cursor, Tree(loc) getTree, TModel(Tree) getTModel, Renamer r) {
    set[Define] defs = {};
    set[loc] uses = {};
    str cursorName = "<cursor[0]>";

    for (loc wsFolder <- r.getConfig().workspaceFolders
       , loc f <- find(wsFolder, "mfun")) {
        Tree t = getTree(f);

        Maybe[TModel] tmodelCache = nothing();
        TModel getLocalTModel() {
            if (tmodelCache is nothing) {
                tmodelCache = just(getTModel(t));
            }
            return tmodelCache.val;
        }

        visit(t) {
            case (ModuleDecl) `module <ModId id> { <Decl* _> }`: {
                if ("<id>" == cursorName) {
                    defs += getLocalTModel().definitions[id.src];
                }
            }
            case (ImportDecl) `import <ModId id>;`: {
                if ("<id>" == cursorName) {
                    uses += id.src;
                }
            }
            case (VarDecl) `def <Id id> : <Type _> = <Expression _>;`: {
                if ("<id>" == cursorName) {
                    defs += getLocalTModel().definitions[id.src];
                }
            }
            case (Expression) `<Id id>`: {
                if ("<id>" == cursorName) {
                    uses += id.src;
                }
            }
        }
    }

    return <defs, uses>;
}

set[loc] findCandidateFiles(set[loc] workspaceFolders) =
    {*ls | loc wsFolder <- workspaceFolders, ls := find(wsFolder, "modules")};

bool tryParse(type[&T <: Tree] tp, str s) {
    try {
        parse(tp, s);
        return true;
    } catch ParseError(_): {
        return false;
    }
}

bool isValidName(moduleId(), str name) = tryParse(#ModId, name);
bool isValidName(variableId(), str name) = tryParse(#Id, name);

bool skipCandidate(set[Define] defs, Tree modTree, Renamer _) {
    // Only if the name of the definition appears in the module, consider it a rename candidate
    set[str] names = {d.id | d <- defs};
    return !(any(/Id t := modTree, "<t>" in names)
          || any(/ModId t := modTree, "<t>" in names));
}

void renameDef(Define def, str newName, TModel tm, Renamer r) {
    if (def.defined in tm.defines.defined) {
        r.textEdit(replace(def.defined, newName));
    }
}

void renameUses(set[Define] defs, str newName, set[loc] useCandidates, TModel tm, Renamer r) {
    set[loc] uses = {occ
        | <Define _:<_, id, orgId, idRole, _, _>,
           use(id, orgId, loc occ, _, {idRole, *_})>
        <- defs * toSet(tm.uses)
    };
    for (loc u <- useCandidates & uses) {
        r.textEdit(replace(u, newName));
    }
}
