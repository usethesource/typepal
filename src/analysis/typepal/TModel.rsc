@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::TModel

/*
    A TModel (for Type Model) is the basic data structure to represent type information.
    It can be extended to suit the needs of a specific type checker.
*/
import String;
import Message;
import Node;
import IO;

import analysis::typepal::Version;
import analysis::typepal::AType;

data AType;

// IdRole: the various (language-specific) roles identifiers can play.
// Initially IdRole is empty but is extended in a language-specific module

data IdRole
    = variableId()
    ;

str prettyRole(IdRole idRole){
    stripped1 = replaceAll(getName(idRole), "Id", "");
    return visit(stripped1) { case /<ch:[A-Z]>/ => toLowerCase(ch) };
}

// PathRole: the various (language-specific) labelled semantic paths
// between program parts
// Initially PathRole is empty but may be extended in a language-specific module

data PathRole;

// ScopeRole: the various (language-specific) roles scopes can play.
// Initially ScopeRole only provides the rootScope but is extended in a language-specific module

data ScopeRole
    = anonymousScope()
    ;

// Applied occurrence (use) of id for given IdRoles
// IdRoles are used to fold multiple scopeGraphs into one
// (e.g., one for class and package names, one for variable names etc.)
data Use
    = use(str id, str orgId, loc occ, loc scope, set[IdRole] idRoles)
    | useq(list[str] ids, str orgId, loc occ, loc scope, set[IdRole] idRoles, set[IdRole] qualifierRoles)
    ;
alias Uses = list[Use];

str getOrgId(Use u) {
    return u.orgId;
}

str getOrgId(Define d) {
    return d.orgId;
}

data ReferPath
    = referToDef(Use use, PathRole pathRole)
    | referToType(loc occ, loc scope, PathRole pathRole)
    ;

alias ReferPaths = set[ReferPath];

// Language-specific auxiliary associated with a name definition
// Extended in a language-specific module

data DefInfo
    = noDefInfo()
    ;

// A single definition: in scope, id is bound in a IdRole to defined, with DefInfo attached
alias Define  = tuple[loc scope, str id, str orgId, IdRole idRole, loc defined, DefInfo defInfo];
alias Defines = set[Define];                                 // All defines
alias Scopes  = map[loc inner, loc outer];                   // Syntactic containment
alias Paths   = rel[loc from, PathRole pathRole, loc to];    // Semantic containment path

data Solver;
data Calculator;
data Requirement;
data TypePalConfig = tconfig();

// The foundation of a TModel. It can be extended in a TypePal application

data TModel (
    str version = getCurrentTplVersion(),
    Defines defines = {},
    Scopes scopes = (),
    Paths paths = {},
    ReferPaths referPaths = {},
    Uses uses = [],
    map[loc, map[str, rel[IdRole idRole, loc defined]]] definesMap = (),
    str modelName = "",
    map[str,loc] moduleLocs = (),
    set[Calculator] calculators = {},
    map[loc,AType] facts = (),
    map[loc,AType] specializedFacts = (),
    set[Requirement] requirements = {},
    rel[loc, loc] useDef = {},
    list[Message] messages = [],
    map[str,value] store = (),
    map[loc, Define] definitions = (),
    map[loc,loc] logical2physical = (),
    bool usesPhysicalLocs = false, // Are locations in physical format?
    TypePalConfig config = tconfig()
)   = tmodel();

@synopsis{Convert logical locations in a TModel to physical locations}
// This function can be written with a single (expensive) visit
// For efficiency reasons, this version avoids visits as much as possible
TModel convertTModel2PhysicalLocs(TModel tm){
    if(tm.usesPhysicalLocs) return tm;

    locMap = tm.logical2physical;
    defines = {};
    definitions = ();
    for(d:<loc scope, str _, str _, IdRole _, loc defined, DefInfo defInfo> <- tm.defines){
        defi = visit(defInfo){ case loc l => locMap[l] when l in locMap };
        d1 = d[scope=(scope in locMap ? locMap[scope] : scope)]
               [defined=(defined in locMap ? locMap[defined] : defined)]
               [defInfo=defi];
        defines += d1;
        definitions[d1.defined] = d1;
    }
    tm.defines = defines;
    tm.definitions = definitions;

    tm.scopes = ( (outer in locMap ? locMap[outer] : outer) : (inner in locMap ? locMap[inner] : inner) 
                | loc outer <- tm.scopes, loc inner := tm.scopes[outer] 
                );
    tm.paths = { <(from in locMap ? locMap[from] : from), 
                  pathRole, 
                  (to in locMap ? locMap[to] : to)> 
               | <loc from, PathRole pathRole, loc to> <- tm.paths 
               };

    tm.referPaths =  visit(tm.referPaths){ case loc l => locMap[l] when l in locMap };
    tm.uses = visit(tm.uses){ case loc l => locMap[l] when l in locMap };
    tm.definesMap = visit(tm.definesMap){ case loc l => locMap[l] when l in locMap };
    tm.moduleLocs = ( key : (l in locMap ? locMap[l] : l) 
                    | key <- tm.moduleLocs, l := tm.moduleLocs[key] 
                    );
    facts = tm.facts;
    tm.facts = ((l in locMap ? locMap[l] : l) 
               : ( (overloadedAType(rel[loc, IdRole, AType] overloads) := atype)
                   ? overloadedAType({ <(l in locMap ? locMap[l] : l), idr, at> | <l, idr, at> <- overloads })
                   : atype)
               | l <- facts, atype := facts[l]
               );
    //tm.facts = visit(tm.facts){ case loc l => locMap[l] ? l };
    tm.specializedFacts =
        ((l in locMap ? locMap[l] : l)
         : ( (overloadedAType(rel[loc, IdRole, AType] overloads) := atype)
             ? overloadedAType({ <(l in locMap ? locMap[l] : l), idr, at> | <l, idr, at> <- overloads })
             : atype)
        | l <- tm.specializedFacts, atype := tm.specializedFacts[l]
        );
    //tm.specializedFacts = visit(tm.specializedFacts){ case loc l => locMap[l] ? l };
    tm.useDef = { < (f in locMap ? locMap[f] : f), 
                    (t in locMap ? locMap[t] : t) > 
                | <f, t> <- tm.useDef };
    // Exlude messages from conversion: otherwise users would see logical locations
    //tm.messages =  visit(tm.messages){ case loc l => locMap[l] ? l };
    tm.store =  visit(tm.store){ case loc l => locMap[l] when l in locMap};
    tm.config = visit(tm.config){ case loc l => locMap[l] when l in locMap};

    tm.usesPhysicalLocs = true;
    return tm;
}

@synopsis{Convert the logical locations in an arbitrary value to physical locations}
value convert2PhysicalLocs(value v, TModel tm){
    locMap = tm.logical2physical;
    return visit(v) { case loc l => locMap[l] when l in locMap};
}

void printTModel(TModel tm){
    println("TModel(");
    println("  defines = {");
    for(Define d <- tm.defines){
        println("    \<<d.scope>, <d.id>, <d.idRole>, <d.defined>\>");
    }
    println("  },");
    println("  facts = (");
    for(loc key <- tm.facts){
        println("    <key>: <tm.facts[key]>");
    }
    println("  ),");
    println("  scopes = (");
    for(loc inner <- tm.scopes){
        println("    <inner>: <tm.scopes[inner]>");
    }
    println("  ),");
    println("  paths = {");
    for(<loc from, PathRole pathRole, loc to> <- tm.paths){
        println("    \<<from>, <pathRole>, <to>\>");
    }
    println("  },");
    println("  referPath = {");
    for(c <- tm.referPaths){
        println("    <c>");
    }
    println("  },");

    println("  uses = [");
    for(Use u <- tm.uses){
        println("    use(<u.ids? ? u.ids : u.id>, <u.occ>, <u.scope>, <u.idRoles>, <u.qualifierRoles? ? u.qualifierRoles : "">)");
    }
    println("  ]");
    println(");");
}