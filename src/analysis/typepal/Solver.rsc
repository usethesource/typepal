@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::Solver

/*
    Implementation of the ISolver interface; this is the API of TypePal's constraint solver
*/
extend analysis::typepal::Collector;
extend analysis::typepal::Messenger;

import Exception;
import IO;
import List;
import Location;
import Map;
import Message;
import Node;
import ParseTree;
import Set;
import String;
import Type;
import analysis::typepal::StringSimilarity;
import util::IDEServices;

void checkAllTypesAvailable(TModel tm){
    for(tup: <loc _, str _, str _, IdRole _, loc _, DefInfo defInfo> <- tm.defines){
        if(!(defInfo has atype)){
            throw "checkTypesAvailable: <tm.modelName>, <tup>";
        }
    }
}

// Implementation of the Solver data type: a collection of call backs

Solver newSolver(Tree pt, TModel tm){
    return newSolver(("newSolver": pt), tm);
}

Solver newSolver(map[str,Tree] namedTrees, TModel tm){

    // Configuration (and related state)

    //bool logSolverSteps = tm.config.logSolverSteps;
    //bool logSolverIterations = tm.config.logSolverIterations;
    //bool logAttempts = tm.config.logAttempts;
    //bool logTModel = tm.config.logTModel;
    //bool logTime = tm.config.logTime;

    //int solverStarted = cpuTime();

    str(str) normalizeName  = defaultNormalizeName;
    bool(AType,AType) isSubTypeFun = defaultIsSubType;

    AType(AType,AType) getLubFun = defaultGetLub;

    AType theMinAType = atypeList([]);
    AType theMaxAType = atypeList([]);

    bool defaultMayOverload(set[loc] defs, map[loc, Define] defines) = false;

    bool (set[loc] defs, map[loc, Define] defines) mayOverloadFun = defaultMayOverload;

    AType (Tree subject, AType def, AType ins, AType act, Solver s) instantiateTypeParameters = defaultInstantiateTypeParameters;

    tuple[list[str] typeNames, set[IdRole] idRoles] (AType atype) getTypeNamesAndRole = defaultGetTypeNamesAndRole;

    AType (Define containerDef, str selectorName, set[IdRole] idRolesSel, Solver s) getTypeInTypeFromDefineFun = defaultGetTypeInTypeFromDefine;

    AType(AType containerType, Tree selector, loc scope, Solver s) getTypeInNamelessTypeFun = defaultGetTypeInNamelessType;

    bool(loc def, TModel tm) reportUnused = defaultReportUnused;

    map[loc,loc] logical2physical = tm.logical2physical;

    map[PathRole, rel[loc,loc]] pathsByPathRole = ();
    for(<loc f, PathRole r, loc t> <- tm.paths){
        pathsByPathRole[r] ? {} += {<f, t>};
    }

    void configTypePal(TypePalConfig tc){

        normalizeName = tc.normalizeName;
        isSubTypeFun = tc.isSubType;
        getLubFun = tc.getLub;
        mayOverloadFun = tc.mayOverload;
        getLubDefined = false;
        try {
            getLubFun(atypeList([]), atypeList([]));
            getLubDefined = true;
        }  catch TypePalUsage(_): {
            getLubDefined = false;
        }

        try {
            theMinAType = tc.getMinAType();
        } catch TypePalUsage(_):{
            if(getLubDefined) throw TypePalUsage("`getMinAType` should be defined when `getLub` is used");
        }

        try {
            theMaxAType = tc.getMaxAType();
        } catch TypePalUsage(_):{
            if(getLubDefined) throw TypePalUsage("`getMaxAType` should be defined when `getLub` is used");
        }

        instantiateTypeParameters = tc.instantiateTypeParameters;
        getTypeNamesAndRole = tc.getTypeNamesAndRole;
        getTypeInTypeFromDefineFun = tc.getTypeInTypeFromDefine;
        getTypeInNamelessTypeFun = tc.getTypeInNamelessType;
        reportUnused = tc.reportUnused;
    }

    TypePalConfig solver_getConfig() = tm.config;

    map[loc, AType] solver_getFacts() = facts;

    Paths solver_getPaths() = tm.paths;

    map[PathRole,rel[loc,loc]] solver_getPathsByPathRole() = pathsByPathRole;

     loc getLogicalLoc(Tree t){
        l = getLoc(t);
        return l in physical2logical ? physical2logical[l] : l;
     }

     loc getLogicalLoc(loc l){
        return l in physical2logical ? physical2logical[l] : l;
     }

    //value _getStore(str key) = tm.store[key];
    //
    //value _putStore(str key, value val) {
    //    tm.store[key] = val;
    //    return val;
    //}

    void solver_push(str key, value val){
        if(key in tm.store && list[value] old := tm.store[key]){
           tm.store[key] = val + old;
        } else {
           tm.store[key] = [val];
        }
    }

    value solver_pop(str key){
        if(key in tm.store && list[value] old := tm.store[key], size(old) > 0){
           pval = old[0];
           tm.store[key] = tail(old);
           return pval;
        } else {
           throw TypePalUsage("Cannot pop from empty stack for key `<key>`");
        }
    }

    value solver_top(str key){
        if(key in tm.store && list[value] old := tm.store[key], size(old) > 0){
           return old[0];
        } else {
           throw TypePalUsage("Cannot get top from empty stack for key `<key>`");
        }
    }

    list[value] solver_getStack(str key){
        if(key in tm.store && list[value] old := tm.store[key]){
            return old;
        }
        return [];
    }

    void solver_clearStack(str key){
        tm.store[key] = [];
    }

    // State of Solver

    map[loc, AType] facts = ();
    map[loc, AType] specializedFacts = ();

    set[Define] defines = {};

    map[loc, Define] definitions = ();

    set[Calculator] calculators = tm.calculators;
    set[Calculator] calculatorJobs = {};
    map[loc, set[Calculator]] triggersCalculator = ();

    set[Requirement] requirements = tm.requirements;
    set[Requirement] requirementJobs = {};
    map[loc, set[Requirement]] triggersRequirement = ();

    set[loc] activeTriggers = {};

    map[loc, set[Use]] def2uses = ();
    map[loc, set[loc]] definedBy = ();
    set[Use] openUses = {};
    set[Use] notYetDefinedUses = {};
    set[loc] doubleDefs = {};

    map[loc, AType] bindings = ();
    list[Message] messages = [];
    list[FailMessage] failMessages = [];

    map[loc,loc] physical2logical = invertUnique(tm.logical2physical);

    set[ReferPath] referPaths = tm.referPaths;

     // Error reporting

    bool solver_report(FailMessage fmsg){
        if(getName(fmsg) == "fm_error"){
           throw checkFailed([fmsg]);
        } else {
            failMessages += fmsg;
            return true;
        }
    }

    bool solver_reports(list[FailMessage] fmsgs){
        if (fmsgs == []) {
            return true;
        }
        if(any(fmsg <- fmsgs, getName(fmsg) == "fm_error")){
            throw checkFailed(fmsgs);
        } else {
            failMessages += fmsgs;
            return true;
        }
    }

    void solver_addMessages(list[Message] msgs){
        failMessages += [ convert(msg) | msg <- msgs ];
    }

    bool solver_reportedErrors(){
        return isEmpty(failMessages) ? false : any(fm <- failMessages, getName(fm) == "fm_error");
    }

    // ---- Register triggers

    void registerCalc(Calculator calc){
        for(dep <- dependsOn(calc)) triggersCalculator[dep] = (triggersCalculator[dep] ? {}) + {calc};
    }

    void registerReq(Requirement req){
        for(dep <- req.dependsOn) triggersRequirement[dep] = (triggersRequirement[dep] ? {}) + {req};
    }

    void addActiveTrigger(loc trigger){
        activeTriggers += trigger;
    }

    void clearActiveTriggers(){
        activeTriggers = {};
    }

    // ---- fire triggers when the type of a location comes available

    void fireTrigger(loc trigger){
        if(trigger in activeTriggers) return;
        addActiveTrigger(trigger);

        for(Calculator calc <- (triggersCalculator[trigger] ? {}) && calc in calculators){
            evalOrScheduleCalc(calc);
        }

        for(Requirement req <- triggersRequirement[trigger] ? {} && req in requirements){
            evalOrScheduleReq(req);
        }

        for(Use u <- (def2uses[trigger] ? {})){
            foundDefs = definedBy[u.occ];
            if({def} := foundDefs, def in facts){
                openUses -= u;
                addFact(u.occ, facts[def]);
            } else {
                if(all(def <- foundDefs, def in facts)){
                   openUses -= u;
                   addFact(u.occ, overloadedAType({<def, definitions[def].idRole, instantiate(facts[def])> | loc def <- foundDefs}));
                }
            }
        }
    }

    // ---- Job management ----------------------------------------------------

    void solvedCalc(Calculator calc){
        calculators -= calc;
        calculatorJobs -= calc;
    }

    void solvedReq(Requirement req){
        requirements -= req;
        requirementJobs -= req;
    }

    // ---- Add a fact --------------------------------------------------------

    bool addFact(loc l, AType atype){
        iatype = instantiate(atype);
        facts[l] = iatype;
        fireTrigger(l);
        return true;
    }

    // ---- evaluating a Define -----------------------------------------------
    // - amounts to creating a new calculator to compute the defined type

    void evalDef(<loc scope, str id, str orgId, IdRole idRole, /*int uid,*/ loc defined, DefInfo defInfo: noDefInfo()>) { }

    void evalDef(<loc scope, str id, str orgId, IdRole idRole, /*int uid,*/ loc defined, DefInfo defInfo: defType(value tp)>) {
        if(AType atype := tp){
            if(solver_isFullyInstantiated(atype)){
                facts[defined] = atype;
            } else {
                calculators += calcType(defined, atype);
            }
        } else if(Tree from := tp){
            fromLoc = getLogicalLoc(from);
            if(fromLoc in facts){
                facts[defined] = facts[fromLoc];
            } else {
                calculators += calcLoc(defined, [fromLoc]);
            }
        }
    }

    void evalDef(<loc scope, str id, str orgId, IdRole idRole, /*int uid,*/ loc defined, DefInfo defInfo: defTypeCall(list[loc] dependsOn, AType(Solver tm) getAType)>){
        calculators += calc(id, defined, dependsOn, getAType);
    }

    void evalDef(<loc scope, str id, str orgId, IdRole idRole, /*int uid,*/ loc defined, DefInfo defInfo: defTypeLub(list[loc] dependsOn, list[loc] defines, list[AType(Solver tm)] getATypes)>){
        calculators += calcLub(id, defines, dependsOn, getATypes);
    }

    list[loc] getDependencies(AType atype){
        list[loc] deps = [];
        visit(atype){
            case tvar(loc src) : deps += src;
        };
        return deps;
    }

    // ---- Evaluate/schedule calculators -------------------------------------

    void evalOrScheduleCalc(Calculator calc){
        try {
            if(evalCalc(calc)){
                solvedCalc(calc);
            } else {
                scheduleCalc(calc);
            }
         } catch checkFailed(list[FailMessage] fmsgs): {
            failMessages += fmsgs;
            solvedCalc(calc);
         }
    }

    void scheduleCalc(Calculator calc, list[loc] dependsOn){
        if(calc in calculators && calc notin calculatorJobs /*&& calc notin solvedCalculatorJobs*/){
            nAvailable = 0;
            for(dep <- dependsOn) { if(dep in facts) nAvailable += 1; }
            enabled = nAvailable == size(dependsOn);
            if(enabled) calculatorJobs += calc;
        }
    }

    void scheduleCalc(calc:calcType(loc src, AType atype)){
        dependsOn = getDependencies(atype) - src; // <===
        scheduleCalc(calc, dependsOn);
    }

    void scheduleCalc(calc:calcLoc(loc src, [loc from])){
        scheduleCalc(calc, [from]);
    }

    void scheduleCalc(calc: calc(str cname, loc src, list[loc] dependsOn, AType(Solver s) getAType)){
        scheduleCalc(calc, dependsOn);
    }

    void scheduleCalc(calc: calcLub(str cname, list[loc] srcs, list[loc] dependsOn, list[AType(Solver s)] getATypes)){
        scheduleCalc(calc, []);
    }

    //map[Calculator, int] calculatorAttempts = ();

    bool evalCalc(calc: calcType(loc src, AType atype)){
        try {
            iatype = instantiate(atype);
            facts[src] = iatype;
            fireTrigger(src);
            if(tvar(l) := iatype){
                facts[l] = facts[src];
                fireTrigger(l);
            }
            return true;
        } catch TypeUnavailable(): return false; /* cannot yet compute type */
    }

    bool evalCalc(calc: calcLoc(loc src, [loc from])){
        try {
            facts[src] = solver_getType(from);
            fireTrigger(src);
            return true;
        } catch TypeUnavailable(): /*return false*/; /* cannot yet compute type */
        return false; // TODO placed return here due to bug in compiler
    }

    bool evalCalc(calc:calc(str cname, loc src, list[loc] dependsOn,  AType(Solver tm) getAType)){
        if(allDependenciesKnown(dependsOn, calc.eager)){
            try {
                facts[src] = instantiate(getAType(thisSolver));
                bindings2facts(bindings);
                fireTrigger(src);
                return true;
            } catch TypeUnavailable(): return false; /* cannot yet compute type */
        }
        return false;
    }

    bool evalCalc(calc: calcLub(str cname, list[loc] defines, list[loc] dependsOn, list[AType(Solver tm)] getATypes)){
        try {
            known = for(getAType <- getATypes){
                        try {
                            tp = getAType(thisSolver);
                            // If the type is overloaded pick the one for a variable
                            if(overloadedAType(rel[loc, IdRole, AType] overloads) := tp){
                                for(<loc _, IdRole idRole, AType tp1> <- overloads){
                                    if(idRole == variableId()){
                                        tp = tp1; break;
                                    }
                                }
                            }
                            append instantiate(tp);
                        } catch TypeUnavailable(): /* type not yet known, continue with others */ ;
                    }

            nknown = size(known);
            if(nknown >= 1){
                tp = simplifyLub(known);
                for(loc def <- defines) {
                    facts[def] = tp;
                }

                if(nknown == size(getATypes)) {
                    for(loc def <- defines) { fireTrigger(def); }
                    return true;
                }
            }
        } catch TypeUnavailable(): return false; /* cannot yet compute type */

        return false;
    }

    default bool evalCalc(Calculator calc) {
        throw TypePalInternalError("evalCalc cannot handle <calc>");
    }

    // ---- evaluate/schedule requirements ------------------------------------

     void evalOrScheduleReq(Requirement req){
        try {
            if(allDependenciesKnown(req.dependsOn, req.eager) && evalReq(req)){
                solvedReq(req);
            } else {
                scheduleReq(req);
            }
        } catch checkFailed(list[FailMessage] fmsgs): {
            failMessages += fmsgs;
            solvedReq(req);
        }
     }

    void scheduleReq(Requirement req){
        if(req in requirements && req notin requirementJobs /*&& req notin solvedRequirementJobs*/){
           nAvailable = 0;
           for(dep <- req.dependsOn) { if(dep in facts) nAvailable += 1; }

           enabled = nAvailable == size(req.dependsOn);
           if(enabled) requirementJobs += req;
       }
    }

    //map[Requirement, int] requirementAttempts = ();

    bool evalReq(req:reqEqual(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!solver_equal(solver_getType(l), solver_getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
    }

    bool evalReq(req:reqComparable(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!solver_comparable(solver_getType(l), solver_getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
    }

    bool evalReq(req:reqSubtype(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!solver_subtype(solver_getType(l), solver_getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
    }

    bool evalReq(req:reqUnify(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!solver_unify(solver_getType(l), solver_getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
    }

    bool evalReq(req:reqError(loc src, list[loc] dependsOn, FailMessage fm)){
        failMessages += fm;
        return true;
    }

    bool evalReq(req:reqErrors(loc src, list[loc] dependsOn, list[FailMessage] fms)){
        failMessages += fms;
        return true;
    }

    bool evalReq(req:req(str rname, loc src,  list[loc] dependsOn, void(Solver s) preds)){
        try {
            preds(thisSolver);
            bindings2facts(bindings);
            solvedReq(req);
            return true;
        } catch TypeUnavailable(): return false;
    }

    // Handle bindings resulting from unification

    // The binding of a type variable that occurs inside the scope of that type variable can be turned into a fact
    void bindings2facts(map[loc, AType] bindings){
        if(!isEmpty(bindings)){
            for(loc b <- bindings){
               addFact(b, bindings[b]);
            }
        }
    }

    // The "run-time" functions that can be called from requirements and calculators

    @doc{
    .Synopsis
    Get type of a tree as inferred by specified type checker

    .Description
    xxx
    }
    //@memo
    AType solver_getType(value v){
        try {
            switch(v){
                case Tree tree:   return instantiate(findType(getLogicalLoc(tree)));
                case tvar(loc l): return facts[getLogicalLoc(l)];
                case AType atype: return instantiate(atype);
                case loc l: {
                        l = getLogicalLoc(l);
                        return l in specializedFacts ? specializedFacts[l] : facts[l];
                }
                case defType(value v) : if(AType atype := v) return atype; else if(Tree tree := v) return instantiate(findType(getLogicalLoc(tree)));
                case Define def:  return solver_getType(def.defInfo);
                case defTypeCall(list[loc] _, AType(Solver s) getAType):
                    return getAType(thisSolver);
                case defTypeLub(list[loc] _, list[loc] _, list[AType(Solver s)] getATypes):
                    return solver_lubList([getAType(thisSolver) | AType(Solver s) getAType <- getATypes]); //throw "Cannot yet handle defTypeLub in getType";
                default:
                    throw "getType cannot handle <v>";
            }

        } catch NoSuchKey(_):
           throw TypeUnavailable();
        throw "getType cannot return type for <v>";
    }

     AType getTypeInScopeFromName0(str name, loc scope, set[IdRole] idRoles){
        u = use(name, name, anonymousOccurrence, scope, idRoles);
        foundDefs = scopeGraph.lookup(u);
        if({def} := foundDefs){
            return instantiate(facts[def]);
        } else {
          if(mayOverloadFun(foundDefs, definitions)){
            overloads = {<d, idRole, instantiate(facts[d])> | loc d <- foundDefs, IdRole idRole := definitions[d].idRole, idRole in idRoles};
            return overloadedAType(overloads);
          } else {
              doubleDefs += foundDefs;             
              msgs = [error(d1, "Double declaration of `<u.orgId>`",
                            causes=[info("Other declaration of `<u.orgId>`", d2) | d2 <- foundDefs, d2 != d1 ]) 
                     | d1 <- foundDefs
                     ];
              solver_reports(msgs);
          }
        }
        throw TypeUnavailable();
    }

    //@memo
    AType solver_getTypeInScopeFromName(str name, loc scope, set[IdRole] idRoles){
        try {
            return getTypeInScopeFromName0(name, getLogicalLoc(scope), idRoles);
        } catch NoSuchKey(value _):
                throw TypeUnavailable();
    }

    AType getTypeInScope0(Tree occ, loc scope, set[IdRole] idRoles){
        orgId = "<occ>";
        id = normalizeName(orgId);
        u = use(id, orgId, getLoc(occ), scope, idRoles);
        foundDefs = scopeGraph.lookup(u);
        if({loc def} := foundDefs){
            addUse({def}, u);
            try {
                return instantiate(facts[def]);
            } catch NoSuchKey(_):
                throw TypeUnavailable();
        } else {
          if(mayOverloadFun(foundDefs, definitions)){
            try {
                overloads = {<d, idRole, instantiate(facts[d])> | d <- foundDefs, idRole := definitions[d].idRole, idRole in idRoles};
                addUse(overloads<0>, u);
                return overloadedAType(overloads);
            } catch NoSuchKey(_):
                 throw TypeUnavailable();
          } else {
             doubleDefs += foundDefs;
             msgs = [error( getLoc(occ), "Double declaration of `<u.orgId>` is applicable here", 
                            causes=[info("Applicable declaration of `<u.orgId>`", d2) | d2 <- foundDefs ]) 
                     ];
             solver_reports(msgs);
          }
        }
        throw TypeUnavailable();
    }

    //@memo
    AType solver_getTypeInScope(Tree occ, loc scope, set[IdRole] idRoles){
        try {
            return getTypeInScope0(occ, getLogicalLoc(scope), idRoles);
        } catch NoSuchKey(_):
            throw TypeUnavailable();
    }

    void addUse(set[loc] defs, Use u){
        for(loc def <- defs){
            if(u.occ in definedBy){  // TODO is this isContainedIn safe to use?
                if(!any(loc d <- definedBy[u.occ], isContainedIn(d, def))){
                     definedBy[u.occ] += {def};
                }
            } else {
                definedBy[u.occ] = {def};
            }
            if(def in def2uses){
                def2uses[def] += {u};
            } else {
                def2uses[def] = {u};
            }
        }
    }

    AType solver_getTypeInType(AType containerType, Tree selector, set[IdRole] idRolesSel, loc scope){
        selectorLoc = getLogicalLoc(getLoc(selector));
        scope = getLogicalLoc(scope);
        selectorOrgName = "<selector>";
        selectorName = normalizeName(selectorOrgName);

        selectorUse = use(selectorName, selectorOrgName, selectorLoc, scope, idRolesSel);
        if(overloadedAType(rel[loc, IdRole, AType] overloads) := containerType){
            rel[loc, IdRole, AType]  valid_overloads = {};
            for(<key, role, tp> <- overloads){
                try {
                    selectorType = solver_getTypeInType(tp, selector, idRolesSel, scope);
                    valid_overloads += <key, role, selectorType>;
                } catch checkFailed(list[FailMessage] _): ; // do nothing and try next overload
                  catch NoBinding(): ; // do nothing and try next overload
            }
            if(isEmpty(valid_overloads)){
                solver_report(error(selector, "Cannot access field on overloaded type %t", containerType));
            } else if({<loc key, IdRole _, AType tp>} := valid_overloads){
                addUse({key}, selectorUse);
                addFact(selectorLoc, tp);
                return tp;
            } else {
                tp2 = overloadedAType(valid_overloads);
                addUse(valid_overloads<0>, selectorUse);
                addFact(selectorLoc, tp2);

                return tp2;
            }
        }
        <containerNames, containerRoles> = getTypeNamesAndRole(containerType);
        ncontainerNames = size(containerNames);
        if(ncontainerNames > 0){
            rel[loc,IdRole,AType] valid_overloads = {};

            int i = 0;
            some_accessible_def = false;
            while(i < ncontainerNames){
                containerName = containerNames[i];
                i += 1;
                all_definitions = solver_getDefinitions(containerName, scope, containerRoles);
                some_accessible_def = some_accessible_def || !isEmpty(all_definitions);
                for(containerDef <- all_definitions){
                    try {
                        selectorType = getTypeInScope0(selector, containerDef.defined, idRolesSel);
                        valid_overloads += <containerDef.defined, containerDef.idRole, instantiateTypeParameters(selector, solver_getType(containerDef.defInfo), containerType, selectorType, thisSolver)>;
                     }
                       catch NoSuchKey(_):
                            ;
                       catch NoBinding(): {
                            try {
                                selectorType = getTypeInTypeFromDefineFun(containerDef, selectorName, idRolesSel, thisSolver);
                                valid_overloads += <containerDef.defined, containerDef.idRole, instantiateTypeParameters(selector, solver_getType(containerDef.defInfo), containerType, selectorType, thisSolver)>;
                            }
                              catch NoBinding():
                                ;
                        }
                 }
                 if(isEmpty(valid_overloads)){
                     if(i == ncontainerNames){
                        if(some_accessible_def)
                            solver_report(error(selector, "No definition found for %v %q in type %t", intercalateOr([prettyRole(idRole) | idRole <- idRolesSel]), "<selector>", containerType));
                        else
                            solver_report(error(selector, "No definition for type %t is available here", containerType));
                     }
                  } else if({<loc key, IdRole _, AType tp>} := valid_overloads){
                    addUse({key}, selectorUse);
                    addFact(selectorLoc, tp);
                    return tp;
                 } else {
                    tp2 = overloadedAType(valid_overloads);
                    addUse(valid_overloads<0>, selectorUse);
                    addFact(selectorLoc, tp2);
                    return tp2;
                 }
            }
         } else {
            try {
                tp2 = getTypeInNamelessTypeFun(containerType, selector, scope, thisSolver);
                addFact(selectorLoc, tp2);
                return tp2;
            } catch NoBinding(): {
                solver_report(error(selector, "No definition for %q in type %t", "<selector>", containerType));
            }
         }
        throw checkFailed([error(selector, "getTypeInType")]);
    }

    rel[str id, AType atype] solver_getAllDefinedInType(AType containerType, loc scope, set[IdRole] idRoles){
        scope = getLogicalLoc(scope);
        <containerNames, containerRoles> = getTypeNamesAndRole(containerType);
        if(!isEmpty(containerNames)){
            containerName = containerNames[0];
            results = {};
            try {
                for(containerDef <- solver_getDefinitions(containerName, scope, containerRoles)){
                    results += { <id, solver_getType(defInfo)> |  <str id, str _orgId, IdRole idRole, loc _, DefInfo defInfo> <- defines[containerDef.defined] ? {}, idRole in idRoles };
                }
                return results;
             } catch AmbiguousDefinition(set[loc] foundDefs): {
                doubleDefs += foundDefs;
                messages += [error("Double declaration of `<getOrgId(definitions[d1])>`", d1, 
                                       causes=[info("Other declaration of `<getOrgId(definitions[d2])>`", d2) | d2 <- foundDefs, d2 != d1 ]) 
                            | d1 <- foundDefs
                            ];
                return results;
             }
         } else {
            throw TypePalUsage("`getAllDefinedInType` is only defined on a named type, found `<prettyAType(containerType)>`");
         }
    }

    set[Define] solver_getDefinitions(str id, loc scope, set[IdRole] idRoles){
        scope = getLogicalLoc(scope);
        try {
            foundDefs = scopeGraph.lookup(use(id, id, anonymousOccurrence, scope, idRoles));
            if({def} := foundDefs){
               return {definitions[def]};
            } else {
              if(mayOverloadFun(foundDefs, definitions)){
                return {definitions[def] | def <- foundDefs};
              } else {
                throw AmbiguousDefinition(foundDefs);
              }
            }
         } catch NoSuchKey(_):
                 throw TypeUnavailable();
           catch NoBinding(): {
                return {};
           }
    }

    set[Define] solver_getAllDefines() = tm.defines;

    Define solver_getDefine(loc l) = definitions[getLogicalLoc(l)];

    rel[loc,loc] solver_getUseDef()
        = { *{<u, d> | loc d <- definedBy[u]} | loc u <- definedBy };

    bool solver_isContainedIn(loc inner, loc outer)
        = isContainedIn(inner, outer, logical2physical);

    bool solver_isBefore(loc l, loc r)
        = isBefore(l, r, logical2physical);

    loc solver_toPhysicalLoc(loc l)
        = l in logical2physical ? logical2physical[l] : l;

    // ---- resolvePath -------------------------------------------------------

    bool resolvePaths(){
        newPaths = {};
        referPaths = tm.referPaths;
        for(ReferPath rp <- referPaths){
            try {
                if(referToDef(Use u, PathRole _) := rp){
                    foundDefs = scopeGraph.lookup(u);
                    if({loc def} := foundDefs){
                       definedBy[u.occ] = foundDefs;
                       newPaths += {<u.scope, rp.pathRole, def>};
                    } else {
                        causes = [ info("Definition of `<u.id>`", d) | d <- foundDefs ];
                        messages += error("Name `<u.id>` is ambiguous", u.occ, causes=causes);
                    }
                    referPaths -= {rp};
                } else {
                    containerType = solver_getType(rp.occ);
                    <containerNames, containerRoles> = getTypeNamesAndRole(containerType);
                    ncontainerNames = size(containerNames);
                    if(ncontainerNames > 0){
                        set[loc] found_scopes = {};

                        int i = 0;
                        some_accessible_def = false;
                        while(i < ncontainerNames){
                            containerName = containerNames[i];
                            i += 1;
                            all_definitions = solver_getDefinitions(containerName, rp.scope, containerRoles);
                            found_scopes = {containerDef.defined | containerDef <- all_definitions};

                             if(isEmpty(found_scopes)){
                                 if(i == ncontainerNames){
                                    solver_report(error(rp.occ, "No definition found for type %t", containerType));
                                 }
                              } else {
                                newPaths += {<rp.scope, rp.pathRole, fscope> | fscope <- found_scopes};
                                referPaths -= {rp};
                                break;
                             }
                        }
                     }
                }
             } catch:{
                ;/* ignore until end */
             }
        }
        newPaths = { tup | tup:<loc u, PathRole _, loc d> <- newPaths, u != d };
        tm.referPaths = referPaths;
        pathsFound = !isEmpty(newPaths);
        if(pathsFound){
            tm.paths += newPaths;
            pathsByPathRole = ();
            for(<loc u, PathRole r, loc d> <- tm.paths){
                pathsByPathRole[r] ? {} += {<u, d>};
            }
        }
        
        return pathsFound;
    }

    // ---- "equal" and "requireEqual" ----------------------------------------

    bool solver_equal(value given, value expected){
        givenType = theMinAType;
        expectedType = theMinAType;
        if(Tree tree := given){
            givenType = solver_getType(tree);
        } else if (AType tp := given){
            givenType = tp;
        } else {
            throw TypePalUsage("`equal` called with <given> and <expected>");
        }
        if(Tree tree := expected){
            expectedType = solver_getType(tree);
        } else if (AType tp := expected){
            expectedType = tp;
        } else {
            throw TypePalUsage("`equal` called with <given> and <expected>");
        }

        if(givenType == expectedType) return true;
        if(solver_isFullyInstantiated(givenType) && solver_isFullyInstantiated(expectedType)){
            return instantiate(unsetRec(givenType)) == instantiate(unsetRec(expectedType));
        } else
            throw TypeUnavailable();
    }

    void solver_requireEqual(value given, value expected, FailMessage fm) {
        if(!solver_equal(given, expected)) solver_report(fm);
    }

    // ---- "unify" and "requireUnify" ----------------------------------------

    bool solver_unify(value given, value expected){
        givenType = theMinAType;
        expectedType = theMinAType;
        if(Tree tree := given){
            givenType = solver_getType(tree);
        } else if (AType tp := given){
            givenType = tp;
        } else {
            throw TypePalUsage("`unify` called with <given> and <expected>");
        }
        if(Tree tree := expected){
            expectedType = solver_getType(tree);
        } else if (AType tp := expected){
            expectedType = tp;
        } else {
            throw TypePalUsage("`unify` called with <given> and <expected>");
        }

        return unify(givenType, expectedType);
    }

    void solver_requireUnify(value given, value expected, FailMessage fm){
        if(!solver_unify(given, expected)) solver_report(fm);
    }

    bool unify(AType given, AType expected){
        bool ok = false;
        <ok, bindings1> = unify(given, expected, bindings);
        if(ok){
            bindings += bindings1;
            return true;
        } else {
            return false;
        }
    }

    // Unification of two types, for now, without checks on variables
    tuple[bool, map[loc, AType]] unify(AType t1, AType t2, map[loc, AType] bindings){
        if(t1 == t2) return <true, bindings>;

        if(tvar(loc tv1) := t1){

            try {
                t11 = findType(tv1);
                if(t11 != t1){
                    if(tm.config.isSubType? && solver_subtype(t11, t1))
                        return <true, bindings>;
                    return unify(t11, t2, bindings);
                }
           } catch NoSuchKey(_):
                ; // unbound, so we will bind it

           return <true, (tv1 : t2) + bindings>;
        }

        if(tvar(loc tv2) := t2){
            try {
                t21 = findType(tv2);
                if(t21 != t2) {
                   if(tm.config.isSubType? && solver_subtype(t21, t2))
                    return <true, bindings>;
                   return unify(t21, t1, bindings);
                }
           } catch NoSuchKey(_):
                ;   // unbound, so we will bind it

           return <true, (tv2 : t1) + bindings>;
        }

        if(atypeList(atypes1) := t1){
           if(atypeList(atypes2) := t2){
              if(size(atypes1) == size(atypes2)){
                for(int i <- index(atypes1)){
                    <res, bindings1> = unify(atypes1[i], atypes2[i], bindings);
                    if(!res) return <res, bindings>;
                    bindings += bindings1;
                }
                return <true, bindings>;
              }
           }
           return <false, ()>;
        }

        // TODO:introducing lazyLub in unify is an interesting idea but is it correct?
        if(lazyLub(lubbables1) := t1 && lazyLub(_) !:= t2){
            for(lb <- toSet(lubbables1)){
                if(tvar(loc tv) := lb){
                   bindings += (tv : t2) + bindings;
                }
            }
            return <true, bindings>;
        }

        if(lazyLub(_) !:= t1 && lazyLub(lubbables2) := t2){
            for(lb <- toSet(lubbables2)){
                if(tvar(loc tv) := lb){
                   bindings += (tv : t1) + bindings;
                }
            }
            return <true, bindings>;
        }
        a1 = arity(t1); a2 = arity(t2);
        if(a1 != a2) return <false, bindings>;
        c1 = getName(t1); c2 = getName(t2);
        if(c1 != c2) return <false, bindings>;

        kids1 = getChildren(t1); kids2 = getChildren(t2);

        for(int i <- [0 .. a1]){
            if(AType k1 := kids1[i], AType k2 := kids2[i]){
                <res, bindings1> = unify(k1, k2, bindings);
                if(!res) return <res, bindings>;
                bindings += bindings1;
            } else {
                if( kids1[i] != kids2[i] ){
                    return <false, bindings>;
                }
            }
        }
        return <true, bindings>;
    }

    // ---- instantiate -------------------------------------------------------

     AType solver_instantiate(AType atype) = instantiate(atype);

    // ---- "subtype" and "requireSubType" ------------------------------------

    bool solver_subtype(value small, value large){
        smallType = theMinAType;
        largeType = theMinAType;
        if(Tree tree := small){
            smallType = solver_getType(tree);
        } else if (AType tp := small){
            smallType = tp;
        } else {
            throw TypePalUsage("`subtype` called with <small> and <large>");
        }
        if(Tree tree := large){
            largeType = solver_getType(tree);
        } else if (AType tp := large){
            largeType = tp;
        } else {
            throw TypePalUsage("`subtype` called with <small> and <large>");
        }

        if(solver_isFullyInstantiated(smallType) && solver_isFullyInstantiated(largeType)){
            return isSubTypeFun(smallType, largeType);
        } else {
            throw TypeUnavailable();
        }
    }

    void solver_requireSubType(value given, value expected, FailMessage fm){
        if(!solver_subtype(given, expected)) solver_report(fm);
    }

    // ---- "comparable" and "requireComparable" ------------------------------

    bool solver_comparable(value given, value expected){
        givenType = theMinAType;
        expectedType = theMinAType;
        if(Tree tree := given){
            givenType = solver_getType(tree);
        } else if (AType tp := given){
            givenType = tp;
        } else {
            throw TypePalUsage("`comparable` called with <given> and <expected>");
        }
        if(Tree tree := expected){
            expectedType = solver_getType(tree);
        } else if (AType tp := expected){
            expectedType = tp;
        } else {
            throw TypePalUsage("`comparable` called with <given> and <expected>");
        }
        if(givenType == expectedType) return true;
        if(solver_isFullyInstantiated(givenType) && solver_isFullyInstantiated(expectedType)){
            return isSubTypeFun(givenType, expectedType) || isSubTypeFun(expectedType, givenType);
        } else {
            throw TypeUnavailable();
        }
    }

    void solver_requireComparable(value given, value expected, FailMessage fm){
        if(!solver_comparable(given, expected)) solver_report(fm);
    }

    // ---- requireTrue and requireFalse --------------------------------------

    void solver_requireTrue(bool b, FailMessage fm){
        if(!b) solver_report(fm);
    }

    void solver_requireFalse(bool b, FailMessage fm){
        if(b) solver_report(fm);
    }

    // ---- lubList -----------------------------------------------------------

    AType solver_lubList(list[AType] atypes) = simplifyLub(atypes);

    // ---- lub ---------------------------------------------------------------

    AType solver_lub(value given, value expected){
        givenType = theMinAType;
        expectedType = theMinAType;
        if(Tree tree := given){
            givenType = solver_getType(tree);
        } else if (AType tp := given){
            givenType = tp;
        } else {
            throw TypePalUsage("`lub` called with <given> and <expected>");
        }
        if(Tree tree := expected){
            expectedType = solver_getType(tree);
        } else if (AType tp := expected){
            expectedType = tp;
        } else {
            throw TypePalUsage("`lub` called with <given> and <expected>");
        }
        return simplifyLub([givenType, expectedType]);
    }

    AType simplifyLub(list[AType] atypes) {
        AType lubbedType = theMinAType;
        list[AType]other = [];
        for(AType t <- atypes){
            if(solver_isFullyInstantiated(t)){
                lubbedType = getLubFun(lubbedType, t);
            } else {
                other += t;
            }
        }

        if(lubbedType != theMinAType){
            bindings1 = bindings;
            bindings = ();
            other = [t | AType t <- other, !unify(lubbedType, t)];
            for(loc b <- bindings){
                addFact(b, bindings[b]);
            }
            bindings = bindings1;
        }
       res = lubbedType;
        switch(size(other)){
            case 0:  res = lubbedType;
            case 1:  res = lubbedType == theMinAType ? other[0] : lazyLub(lubbedType + other);
            default: res = lubbedType == theMinAType ? lazyLub(other) : lazyLub(lubbedType + other);
        }
        return res;
    }

    // ---- The "fact" assertion ----------------------------------------------

    void fact(value v, AType atype){
        if(Tree t := v) {
            addFact(getLogicalLoc(t), atype);
         } else if(loc l := v){
            addFact(getLogicalLoc(l), atype);
         } else {
            throw TypePalUsage("First argument of `fact` should be `Tree` or `loc`, found `<typeOf(v)>`");
         }
    }

    void solver_specializedFact(value v, AType atype){
        if(Tree t := v) {
            specializedFacts[getLogicalLoc(t)] = atype;
         } else if(loc l := v){
            specializedFacts[getLogicalLoc(l)] = atype;
         } else {
            throw TypePalUsage("First argument of `specializedFact` should be `Tree` or `loc`, found `<typeOf(v)>`");
         }
    }

    bool allDependenciesKnown(set[loc] deps, bool eager){
        if(isEmpty(deps)) return true;
        if(eager) return all(dep <- deps, dep in facts);
        return all(dep <- deps, 
                   dep in facts,
                   solver_isFullyInstantiated(facts[dep]));
    }

    bool allDependenciesKnown(list[loc] deps, bool eager){
        if(isEmpty(deps)) return true;
        if(eager) return all(dep <- deps, dep in facts);
        return all(dep <- deps, 
                   dep in facts, 
                   solver_isFullyInstantiated(facts[dep]));
    }

    bool solver_isFullyInstantiated(AType atype){
        visit(atype){
            case tvar(loc tname): { tname = getLogicalLoc(tname);
                                    if(tname notin facts) return false;
                                    if(tvar(_) := facts[tname]) return false;
                                  }
            case lazyLub(list[AType] atypes):
                    if(!(isEmpty(atypes) || all(AType tp <- atype, solver_isFullyInstantiated(tp)))) return false;
            case overloadedAType(rel[loc, IdRole, AType] overloads):
                    if(!all(<_, _, tp> <- overloads, solver_isFullyInstantiated(tp))) return false;
        }
        return true;
    }

    // Find a (possibly indirectly defined) type for src
    AType findType(loc src){
        if(src in bindings){
            v = bindings[src];
            if(tvar(loc src1) := v && src1 != src && (src1 in bindings || src1 in facts)) return findType(src1);
            return v;
        }
        if(src in facts){
            v = src in specializedFacts ? specializedFacts[src] : facts[src];
            if(tvar(loc src1) := v && src1 != src && (src1 in bindings || src1 in facts)) return findType(src1);
            return v;
        }
       throw NoSuchKey(src);
    }

    // Substitute a type variable first using bindings, then facts; return as is when there is no binding
    AType substitute(tv: tvar(loc src)){
        if(src in bindings) { b = bindings[src]; return b == tv ? tv : substitute(b); }
        if(src in facts) { b = facts[src]; return b == tv ? tv : substitute(b); }
        return tv;
    }

    default AType substitute(AType atype){
            return atype;
    }

    // Recursively instantiate all type variables and lazyLubs in a type
    AType instantiate(AType atype){
      xx =
          visit(atype){
            case tv: tvar(_) => substitute(tv)
            case lazyLub(list[AType] atypes) : {
                list[AType] sbs = [substitute(tp) | AType tp <- atypes];
                insert simplifyLub(sbs);
                }
          };
      return xx;
    }

    /*
     *  run: validates an extracted TModel via constraint solving
     *
     */
    TModel solver_run(){
        tm = tm.config.preSolver(namedTrees, tm);

        configTypePal(tm.config);

        // Initialize local state of Solver

        facts = tm.facts;
        defines = tm.defines;
        definesAdded = false;
        definitions = tm.definitions;
        bindings = ();
        messages = tm.messages;
        failMessages = [];

        resolvePaths();

        // Check that all uses have a definition and that all overloading is allowed

        set[loc] actuallyUsedDefs = {};
        for(Use u <- tm.uses){
            try {
               foundDefs = scopeGraph.lookup(u);
               foundDefs = { fd | fd <- foundDefs, definitions[fd].idRole in u.idRoles };
               actuallyUsedDefs += foundDefs;
               if(isEmpty(foundDefs)){
                    throw NoBinding();
               } else
               if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                  definedBy[u.occ] = foundDefs;
                  for(def <- foundDefs) def2uses[def] = (def2uses[def] ? {}) + u;
                  openUses += u;
                } else {
                    doubleDefs += foundDefs;
                    messages += [error("Multiple declarations of `<u.orgId>` are applicable here", u.occ, 
                                       causes=[info("Declaration of `<u.orgId>`", d2) | d2 <- foundDefs]) 
                                ];
                }
            }
            catch NoBinding(): {
                //println("<tm.modelName>: NoBinding: <u>");
                notYetDefinedUses += u;
            }
            catch TypeUnavailable(): {
                notYetDefinedUses += u;
            }
        }

        // Check for illegal overloading of unused definitions
        set[loc] unusedDefs = domain(definitions) - actuallyUsedDefs;

        for(ud <- unusedDefs){
            udef = definitions[ud];

            scope = udef.scope;
            id = udef.id;
            orgId = udef.orgId;
            idRole = udef.idRole;
            defined = udef.defined;
            //if(defined in logical2physical) defined = logical2physical[defined];

            u = use(id, orgId, defined, scope, {idRole}); // turn each unused definition into a use and check for double declarations;
            try {
               foundDefs = scopeGraph.lookup(u);
                if(isEmpty(foundDefs)){
                    ;//throw TypePalInternalError("No binding found while checking for double definitions");
               } else
               if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                 ;
                } else {
                    doubleDefs += foundDefs;
                    messages += [error("Double declaration of `<u.orgId>`", d1, 
                                       causes=[info("Other declaration of `<u.orgId>`", d2) | d2 <- foundDefs, d2 != d1 ]) 
                                | d1 <- foundDefs, isContainedIn(u.scope, definitions[d1].scope, logical2physical)
                                ];
                }
            }
            catch NoBinding(): {
                ;//throw TypePalInternalError("No binding found while checking for double definitions");
            }
        }

        unusedDefs = actuallyUsedDefs = {};

        // Process all defines (which may create new calculators/facts)

        for(Define def <- defines){
            try {
                evalDef(def);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
            }
        }

        // Register all dependencies

        for(Calculator calc <- calculators){
            registerCalc(calc);
        }

        for(Requirement req <- requirements){
            registerReq(req);
        }

        // See what the facts derived sofar can trigger
        for(fct <- facts){
            try {
                fireTrigger(fct);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
            }
        }

        // Try to evaluate or schedule the calculators

        for(Calculator calc <- calculators){
            try {
            	clearActiveTriggers();
                evalOrScheduleCalc(calc);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
            }
        }

        // Try to evaluate or schedule the requirements

        for(Requirement req <- requirements){
            try {
                clearActiveTriggers(); // ? needed
                evalOrScheduleReq(req);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
             }
        }

        // Here we have jobs for calculators and requirements with known dependencies

        /****************** main solve loop *********************************/

        int iterations = 0;
        int ncalculators = size(calculators);
        int nrequirements = size(requirements);
        int nfacts = size(facts);
        int nopenUses = size(openUses);
        int nreferPaths = size(referPaths);

        solve(nreferPaths, ncalculators, nrequirements, nfacts, nopenUses){
            iterations += 1;

            // ---- referPaths

            resolvePaths();

            for(u <- notYetDefinedUses){
                try {
                   foundDefs = scopeGraph.lookup(u);
                    if(isEmpty(foundDefs)){
                        throw NoBinding();
                   } else
                   if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                      definedBy[u.occ] = foundDefs;
                      for(def <- foundDefs) def2uses[def] = (def2uses[def] ? {}) + u;
                      openUses += u;
                      notYetDefinedUses -= u;

                      if({def} := foundDefs, def in facts){
                        openUses -= u;
                        addFact(u.occ, facts[def]);
                      } else {
                        if(all(def <- foundDefs, def in facts)){
                            openUses -= u;
                            addFact(u.occ, overloadedAType({<def, definitions[def].idRole, instantiate(facts[def])> | loc def <- foundDefs}));
                        }
                      }
                    } else {
                        messages += [error("Multiple declarations of `<u.orgId>` apply here", u.occ, 
                                           causes=[info("Declaration of `<u.orgId>`", d2) | d2 <- foundDefs]) 
                                    ];
                    }
                } catch NoBinding(): {
                    ; //ignore until end
                } catch TypeUnavailable() : {
                    ; // ignore until end
                }
            }


            // ---- calculatorJobs

            for(Calculator calc <- calculatorJobs){
                 try {
                 	clearActiveTriggers();
                    if(evalCalc(calc)){
                       solvedCalc(calc);
                    }
                 } catch checkFailed(list[FailMessage] fms): {
                        failMessages += fms;
                        solvedCalc(calc);
                 }
            }

            // ---- requirementJobs

            for(Requirement req <- requirementJobs){
                try {
                    clearActiveTriggers(); // ? needed
                    if(evalReq(req)){
                        solvedReq(req);
                    }
                } catch checkFailed(list[FailMessage] fms): {
                    failMessages += fms;
                    solvedReq(req);
                }
            }

            ncalculators = size(calculators);
            nrequirements = size(requirements);
            nfacts = size(facts);
            nopenUses = size(openUses);
            nreferPaths = size(referPaths);
        }

        /****************** end of main solve loop *****************************/

        // Eliminate all defTypeCalls before handing control to the postSolver
        for(loc l <- definitions){
            Define def = definitions[l];
            if(defTypeCall(_, AType(Solver s) getAType) := def.defInfo){
                kwparams = getKeywordParameters(def.defInfo);
                try {
                    di = defType(getAType(thisSolver));
                    def.defInfo = setKeywordParameters(di, kwparams);
                    definitions[l] = def;
                } catch _: { // Guard against type incorrect defines, but record for now
                    ; //println("Skipping (type-incorrect) def: <def>\n");
                }
            }
        }
        tm.definitions = definitions;

        newDefines =
            for(def <- defines){
                if(defTypeCall(_, AType(Solver s) getAType) := def.defInfo){
                    kwparams = getKeywordParameters(def.defInfo);
                    try {
                        di = defType(getAType(thisSolver));
                        def.defInfo = setKeywordParameters(di, kwparams);
                    } catch _: { // Guard against type incorrect defines, but record for now
                        ; //println("Skipping (type-incorrect) def: <def>\n");
                    }
                }
                append def;
            }
        tm.defines = toSet(newDefines);

        tm.config.postSolver(namedTrees, thisSolver);

        // Convert all FaillMessages into Messages
        for(fm <- failMessages){
            messages += toMessage(fm, solver_getType);
        }

        for(Use u <- openUses){
            try {
                 foundDefs = scopeGraph.lookup(u);
             } catch NoBinding(): {
                roles = size(u.idRoles) > 5 ? "" : intercalateOr([prettyRole(idRole) | idRole <- u.idRoles]);
                msg =  error("Undefined <roles> `<getOrgId(u)>`", u.occ);
                if(tm.config.enableErrorFixes){
                    msg.fixes = undefinedNameProposals(u, tm);
                }
                messages += msg;
             }
        }

        for(u <- notYetDefinedUses){
            roles = size(u.idRoles) > 5 ? "" : intercalateOr([prettyRole(idRole) | idRole <- u.idRoles]);
            msg = error("Undefined <roles> `<getOrgId(u)>`", u.occ);
            if(tm.config.enableErrorFixes){
                msg.fixes = undefinedNameProposals(u, tm);
            }
            messages += msg;
        }

        error_locations = { src | error(_,loc src) <- messages };

        for(rp <- referPaths){
            switch(rp){
            case referToDef(_, _):
                if(rp.use.occ notin error_locations){
                    messages += error("Reference to name `<rp.use.id>` cannot be resolved", rp.use.occ);
                }
            case referToType(occ, _, _):
                if(occ notin error_locations){
                    messages += error("Reference to type definition cannot be resolved", occ);
                }
            }
        }

        errors = { e | e:error(_,_) <- messages };

        realErrorsFound = !isEmpty(errors);

        reportedLocations = { msg.at | msg <- messages };

        //if(nopenUses + ncalculators + nrequirements > 0){
        //    println("<tm.modelName>, REMAINING <nopenUses> uses; <ncalculators> calculators; <nrequirements> requirements");
        //    //printSolverState();
        //}

        // Only report "derived" messages when no real errors were found
        if(!realErrorsFound){
            for (Use u <- openUses) {
                foundDefs = definedBy[u.occ];
                for(_ <- foundDefs, u.occ notin facts, !alreadyReported(messages, u.occ)) {
                    messages += error("Unresolved type for `<u has id ? u.id : u.ids>`", u.occ);
                }
            }

            calcNoLubs = [calc | calc <- calculators, !(calc is calcLub)];

            for(Calculator clc <- sort(calcNoLubs, bool(Calculator a, Calculator b){ 
                return (a.src in logical2physical ? logical2physical[a.src] : a.src).length 
                         < (b.src in logical2physical ? logical2physical[b.src] : b.src).length; })){
                src = clc.src;
                if(src notin facts, !alreadyReported(messages, src)){
                    set[loc] cdeps = toSet(dependsOn(clc));
                    if(src notin facts && isEmpty(reportedLocations & cdeps)){
                        messages += error("Unresolved type<clc has cname ? " for <clc.cname>" : "">", src);
                        reportedLocations += src;
                    }
                }
            }

            calcLubs = [calc | calc <- calculators, calc is calcLub];
            for(Calculator clc <- calcLubs){
                csrcs = srcs(clc);
                set[loc] cdeps = toSet(dependsOn(clc));
                for(loc src <- csrcs){
                    if(src notin facts && isEmpty(reportedLocations & cdeps)){
                        messages += error("Unresolved type<clc has cname ? " for <clc.cname>" : "">", src);
                        reportedLocations += src;
                    }
                }
            }

            for(Requirement req <- requirements){
                src =  getReqSrc(req);
                if(isEmpty(reportedLocations & toSet(req.dependsOn)) && !alreadyReported(messages, src)){
                    messages += error("Invalid <req.rname>; type of one or more subparts could not be inferred", src);
                    reportedLocations += src;
                }
            }
        }

        tm.calculators = calculators;
        tm.requirements = requirements;

        tm.facts = facts;
        // prune the definedBy relation using specialized facts
        for(loc u <- specializedFacts){
            orgtp = facts[u];
            spectp = specializedFacts[u];
            if(u in definedBy && overloadedAType(org_overloads) := orgtp){
                if(overloadedAType(spec_overloads) := spectp){
                    definedBy[u] = { def | <def, _, otype> <- org_overloads, otype in spec_overloads<2>};
                } else {
                    definedBy[u] = { def | <def, _, otype> <- org_overloads, otype == spectp};
                }
            }
          }

        tm.specializedFacts = specializedFacts;

        //println("definedBy;"); iprintln(definedBy);
        tm.useDef = { *{<u, d> | loc d <- definedBy[u]} | loc u <- definedBy };

        ldefines = for(tup: <loc _, str _, str _, IdRole _, loc defined, DefInfo defInfo> <- tm.defines){
                        if(defInfo has tree){
                            l = getLogicalLoc(defInfo.tree);
                            if(l in tm.facts){
                                   dt = defType(tm.facts[l]);
                                   tup.defInfo = setKeywordParameters(dt, getKeywordParameters(defInfo));
                            } else {
                                continue;
                            }
                        } else {
                            if(defined in tm.facts){
                                dt = defType(tm.facts[defined]);
                                tup.defInfo = setKeywordParameters(dt, getKeywordParameters(defInfo));
                            } else {
                                continue;
                            }
                         }
                         append tup;
                      };
        tm.defines = toSet(ldefines);

        for(Define def <- tm.defines){
            defdefined = solver_toPhysicalLoc(def.defined);
            if(defdefined notin def2uses && defdefined notin doubleDefs && reportUnused(defdefined, tm)){
                messages += warning("Unused <prettyRole(def.idRole)> `<def.id>`", defdefined);
            }
        }
        messages =  visit(messages) { case loc l => solver_toPhysicalLoc(l) };
        tm.messages = sortMostPrecise(toList(toSet(messages)));

        checkAllTypesAvailable(tm);
        return tm;
    }

    // The actual code of newSolver

    ScopeGraph scopeGraph = newScopeGraph(tm, tm.config);
    Solver thisSolver = dummySolver();

    thisSolver =
            solver(
            /* Lifecycle */     solver_run,
            /* Types */         solver_getType,
                                solver_getTypeInScope,
                                solver_getTypeInScopeFromName,
                                solver_getTypeInType,
                                solver_getAllDefinedInType,
           /*Fact */            fact,
                                solver_specializedFact,
          /* Calculate & Require */
                                solver_equal,
                                solver_requireEqual,
                                solver_unify,
                                solver_requireUnify,
                                solver_comparable,
                                solver_requireComparable,
                                solver_subtype,
                                solver_requireSubType,
                                solver_lub,
                                solver_lubList,
                                solver_requireTrue,
                                solver_requireFalse,
           /* Inference */      solver_instantiate,
                                solver_isFullyInstantiated,
           /* Reporting */      solver_report,
                                solver_reports,
                                solver_addMessages,
                                solver_reportedErrors,
           /* Global Info */    solver_getConfig,
                                solver_getFacts,
                                solver_getPaths,
                                solver_getPathsByPathRole,
                                solver_getDefinitions,
                                solver_getAllDefines,
                                solver_getDefine,
                                solver_getUseDef,
                                solver_isContainedIn,
                                solver_isBefore,

          /* Nested Info */     solver_push,
                                solver_pop,
                                solver_top,
                                solver_getStack,
                                solver_clearStack
                     );

    scopeGraph.setSolver(thisSolver); // This breaks the circular dependency between ScopeGraph and Solver

    return thisSolver;
}

// CodeActions for errors generated by Solver

list[CodeAction] undefinedNameProposals(Use u, TModel tm)
    =
    [ action(
        title="Replace by `<prop>`", 
        edits=[changed([replace(u.occ, prop)])]
      )
    | str prop <- tm.config.similarNames(u, tm)
    ];