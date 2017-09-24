module rascal::Scope

extend typepal::TypePal;
extend typepal::TestFramework;
import Relation;

data IdRole
    = moduleId()
    | functionId()
    | variableId()
    | formalId()
    | labelId()
    | constructorId()
    | dataId()
    ;

data PathRole
    = importPath()
    | extendPath()
    ;

data Vis
    = publicVis()
    | privateVis()
    | defaultVis()
    ;

data Modifier
    = javaModifier()
    | testModifier()
    | defaultModifier()
    ;

// Add visibility information to definitions
data DefInfo(Vis vis = publicVis());

// Maintain conditionalScopes: map to subrange where definitions are valid
public map[Key,Key] elseScopes = ();

void addElseScope(Tree cond, Tree elsePart){
    elseScopes[getLoc(cond)] = getLoc(elsePart);
}

// Define the name overloading that is allowed
bool myMayOverload(set[Key] defs, map[Key, Define] defines){
    //println("myMayOverload: <defs>");
    idRoles = {defines[def].idRole | def <- defs};
    //println("idRoles: <idRoles>");
    return idRoles <= {functionId(), constructorId()} || idRoles == {dataId()};
}

// Enhance FRModel with transitive edges for extend
FRModel myEnhanceFRModel(FRModel m){
    extendPlus = {<from, to> | <Key from, extendPath(), Key to> <- m.paths}+;
    extended = domain(extendPlus);
    m.paths += { <from, extendPath(), to> | <Key from, Key to> <- extendPlus};
    m.paths += { <c, importPath(), a> | < Key c, importPath(), Key b> <- m.paths,  <b , extendPath(), Key a> <- m.paths};
    return m;
}

// Name resolution filters

Accept isAcceptableSimple(FRModel frm, Key def, Use use){
    
    //println("isAcceptableSimple: <use.id> def=<def>, use=<use>");
    res = acceptBinding();

    if(variableId() in use.idRoles){
       // enforce definition before use
       if(def < use.scope && use.occ.offset < def.offset){
           res = ignoreContinue();
           //println("isAcceptableSimple =\> <res>");
           return res;
       }
       // restrict when in conditional scope
       if(elseScopes[use.scope]?){
          if(use.occ < elseScopes[use.scope]){
             res = ignoreContinue();
             //println("isAcceptableSimple =\> <res>");
             return res;
          }
       }
    }
    //println("isAcceptableSimple =\> <res>");
    return res;
}

Accept isAcceptablePath(FRModel frm, Key defScope, Key def, Use use, PathRole pathRole) {
    //println("isAcceptablePath <use.id>, candidate <def>, <pathRole>, <use>");
    res = acceptBinding();
    vis = frm.definitions[def].defInfo.vis;
    //println("vis: <vis>");
    if(pathRole == importPath()){
        defIdRole = frm.definitions[def].idRole;
        res = (defIdRole == dataId() || defIdRole == constructorId()) // data declarations and constructors are globally visible
              || (<use.scope, importPath(), defScope> in frm.paths // one step import only
                  && vis == publicVis())
              ? acceptBinding() 
              : ignoreContinue();
    }
    if(pathRole == extendPath()){
        res = acceptBinding();
    }
    //println("isAcceptablePath =\> <res>");
    return res;
}
