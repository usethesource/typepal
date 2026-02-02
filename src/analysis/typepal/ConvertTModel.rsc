module analysis::typepal::ConvertTModel

import analysis::typepal::TModel;
import analysis::typepal::AType;

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
