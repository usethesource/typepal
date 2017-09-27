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
public rel[Key,Key] elseScopes = {};

void addElseScope(Tree cond, Tree elsePart){
    elseScopes += <getLoc(cond), getLoc(elsePart)>;
}

// Define the name overloading that is allowed
bool myMayOverload(set[Key] defs, map[Key, Define] defines){
    //println("myMayOverload: <defs>");
    idRoles = {defines[def].idRole | def <- defs};
    //println("idRoles: <idRoles>");
    return idRoles <= {functionId(), constructorId()} || idRoles == {dataId()};
}

// Enhance FRModel before validation
FRModel myPreValidation(FRModel m){
    // add transitive edges for extend
    extendPlus = {<from, to> | <Key from, extendPath(), Key to> <- m.paths}+;
    extended = domain(extendPlus);
    m.paths += { <from, extendPath(), to> | <Key from, Key to> <- extendPlus};
    m.paths += { <c, importPath(), a> | < Key c, importPath(), Key b> <- m.paths,  <b , extendPath(), Key a> <- m.paths};
    // check for parameter arity of ADTs
  
        return m;
}

// Enhance FRModel after validation
FRModel myPostValidation(FRModel m){
    // Check that all uses of an adt name are defined
    adts = {<adtName, size(params), def> | <def, di> <- m.defines[_,_,dataId()], aadt(str adtName, params, bound) := di.atype};
    for(adtName <- adts<0>){
        nparams = adts[adtName]<0>;
        if(size(nparams) != 1){
            for(def <- adts[adtName,_]){
                m.messages += { error("Type <fmt(adtName)> defined with <fmt(sort(nparams))> type parameters", def) };
            }
        }
    }
    // Check that all adt uses have the correct number of type parameters
    adtNames = domain(adts);
    msgs = {};
    for(def <- m.facts){
        tp = m.facts[def];
        if(a:aadt(adtName,params, _) := tp){
           if(adtName notin adtNames){
               msgs += {error("Undeclared type <fmt(adtName)>", def)};
            } else
            if({nexpected} := adts[adtName]<0> && nexpected != size(params)){
                msgs += {error("Expected <fmt(nexpected, "type parameter")> for <fmt(adtName)>", def)};
            }
        }
    }
    m.messages += filterMostGlobal(msgs);
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
       set[Key] elseParts = elseScopes[use.scope];
       println("elseParts = <elseParts>, <any(part <- elseParts, use.occ < part)>");
       if(!isEmpty(elseParts)){
          if(any(part <- elseParts, use.occ < part)){
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
