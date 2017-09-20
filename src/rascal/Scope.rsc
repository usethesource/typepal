module rascal::Scope

extend typepal::TypePal;

data IdRole
    = moduleId()
    | functionId()
    | variableId()
    | formalId()
    | labelId()
    | constructorId()
    ;

public set[IdRole] possibleOverloads = {functionId(), constructorId()};

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

// Name resolution filters

Accept isAcceptableSimple(FRModel frm, Key def, Use use){
    
    //println("isAcceptableSimple: id=<use.id> def=<def>, use=<use>");
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

Accept isAcceptablePath(FRModel frm, Key def, Use use, PathRole pathRole) {
    println("isAcceptablePath <def>, <use>, <pathRole>");
    res = acceptBinding();
    vis = frm.definitions[def].defInfo.vis;
    println("vis: <vis>");
    if(pathRole == importPath()){
        res = vis == publicVis() ? acceptBinding() : ignoreContinue();
    }
    if(pathRole == extendPath()){
        res = acceptBinding();
    }
    println("isAcceptablePath =\> <res>");
    return res;
}
