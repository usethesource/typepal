module analysis::typepal::TModel

import String;
import Message;
import List;
import Node;
import IO;

import analysis::typepal::Version;

data AType;

// IdRole: the various (language-specific) roles identifiers can play.
// Initially IdRole is empty but is extended in a language-specific module

data IdRole
    = variableId()
    ;

str prettyRole(IdRole idRole){
    stripped1 = replaceAll(getName(idRole), "Id", "");
    return visit(stripped1) { case /<ch:[A-Z]>/ => " " + toLowerCase(ch) };
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
    TypePalConfig config = tconfig()
)   = tmodel();
 
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