module analysis::typepal::Solver

import Set; 
import Node;
import Map;
import IO;
import List; 
import Location;
import ParseTree;
import Type;
import String;
import Message;
import Exception;
import util::Benchmark;

extend analysis::typepal::AType;
extend analysis::typepal::Collector;
extend analysis::typepal::Exception;
extend analysis::typepal::FailMessage;
extend analysis::typepal::Messenger;
extend analysis::typepal::ScopeGraph;
extend analysis::typepal::TypePalConfig;
extend analysis::typepal::Utils;

extend analysis::typepal::ISolver;

//// The Solver data type: a collection of call backs
//
//data Solver
//    = solver(
//    /* Lifecycle */     TModel () run,
//    /* Types */         AType(value) getType,
//                        AType (Tree occ, loc scope, set[IdRole] idRoles) getTypeInScope,
//                        AType (str name, loc scope, set[IdRole] idRoles) getTypeInScopeFromName,
//                        AType (AType containerType, Tree selector, set[IdRole] idRolesSel, loc scope) getTypeInType,
//                        rel[str id, AType atype] (AType containerType, loc scope, set[IdRole] idRoles) getAllDefinedInType,
//    /* Fact */          void (value, AType) fact,
//                        void (value, AType) specializedFact,
//    /* Calculate & Require */    
//                        bool (value, value) equal,
//                        void (value, value, FailMessage) requireEqual,
//       
//                        bool (value, value) unify,
//                        void (value, value, FailMessage) requireUnify,
//        
//                        bool (value, value) comparable,
//                        void (value, value, FailMessage) requireComparable,
//                        
//                        bool (value, value) subtype,
//                        void (value, value, FailMessage) requireSubType,
//                        
//                        AType (value, value) lub,
//                        AType (list[AType]) lubList,
//        
//                        void (bool, FailMessage) requireTrue,
//                        void (bool, FailMessage) requireFalse,
//        
//    /* Inference */     AType (AType atype) instantiate,
//                        bool (AType atype) isFullyInstantiated,
//    
//    /* Reporting */     bool(FailMessage fm) report,
//                        bool (list[FailMessage]) reports,
//                        void (list[Message]) addMessages,
//                        bool () reportedErrors,
//    /* Global Info */   TypePalConfig () getConfig,
//                        map[loc, AType]() getFacts,
//                        Paths() getPaths,
//                        value (str key) getStore,
//                        value (str key, value val) putStore,
//                        set[Define] (str id, loc scope, set[IdRole] idRoles) getDefinitions,    // deprecated
//                        set[Define] () getAllDefines,
//                        Define(loc) getDefine
//    );
   
Solver newSolver(Tree pt, TModel tm){
    return newSolver(("newSolver": pt), tm);
}

Solver newSolver(map[str,Tree] namedTrees, TModel tm){
    
    // Configuration (and related state)
    
    bool logSolverSteps = tm.config.logSolverSteps;
    bool logSolverIterations = tm.config.logSolverIterations;
    bool logAttempts = tm.config.logAttempts;
    bool logTModel = tm.config.logTModel;
    bool logTime = tm.config.logTime;
    
    int solverStarted = cpuTime();
    
    str(str) unescapeName  = defaultUnescapeName;
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
    
    void configTypePal(TypePalConfig tc){
        
        unescapeName = tc.unescapeName;
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
    
    TypePalConfig _getConfig() = tm.config;
    
    map[loc, AType] _getFacts() = facts;
    
    Paths _getPaths() {
        res = tm.paths;
        return res;
     }
    
    value _getStore(str key) = tm.store[key];
    
    value _putStore(str key, value val) { 
        tm.store[key] = val;  
        return val;
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
    
    map[loc, AType] bindings = ();
    list[Message] messages = [];
    list[FailMessage] failMessages = [];
    
    set[ReferPath] referPaths = tm.referPaths;
    
    // ---- printing
    
    void printSolverState(){
        println("\nDERIVED FACTS");
            for(loc fact <- facts){
                println("\t<fact>: <facts[fact]>");
            }
        if(size(requirements) + size(calculators)  + size(openUses) > 0){
            println("\nUNRESOLVED");
          
            for(Requirement req <- requirements){
                print(req in requirementJobs ? "*" : " ");
                print(req, "\t", facts);
            }
            
            for(Calculator calc <- calculators){
                print(calc in calculatorJobs ? "*" : " ");
                print(calc, "\t", facts);
            }
            
            for(Use u <- openUses){
                println("\t<u>");
            }
         }
    }
    
    void printDef2uses(){
        if(!isEmpty(def2uses)) println("\nDEFINE TO USES");
        for(def <- def2uses){
            println("\t<def> ==\> <def2uses[def]>");
        }
    }
    
    void printUse2Def(){
        if(!isEmpty(definedBy)) println("\nUSE TO DEFINES");
        for(occ <- definedBy){
            println("\t<occ> ==\> <definedBy[occ]>");
        }
    }
    
     // Error reporting
    
    bool _report(FailMessage fmsg){
        if(getName(fmsg) == "_error"){
           throw checkFailed([fmsg]);
        } else {
            failMessages += fmsg;
            return true;
        }
    }
    
    bool _reports(list[FailMessage] fmsgs){
        if (fmsgs == []) {
            return true;
        }
        if(any(fmsg <- fmsgs, getName(fmsg) == "_error")){
            throw checkFailed(fmsgs);
        } else {
            failMessages += fmsgs;
            return true;
        }
    }
    
    void _addMessages(list[Message] msgs){
        failMessages += [ convert(msg) | msg <- msgs ];
    }
    
    bool _reportedErrors(){
        return isEmpty(failMessages) ? false : any(fm <- failMessages, getName(fm) == "_error");
    }
    
    // ---- validation
    
    void validateTriggers(){
        int nissues = 0;
        for(Calculator calc <- calculators){
            deps = calcType(loc src, AType atype) := calc ? getDependencies(atype) : calc.dependsOn;
            
            for(loc dep <- deps){
                if(!(facts[dep]? || calc in (triggersCalculator[dep] ? {}))){
                    println("Not a fact or trigger for: <dep>");
                    print(calc, "\t", facts);
                    println("\t<calc>");
                    nissues += 1;
                }
            }
        }
    
        for(Requirement req <- requirements){
            for(loc dep <- req.dependsOn){
                if(!(facts[dep]? || req in (triggersRequirement[dep] ? {}))){
                    println("Not a fact or trigger for dependency on: <dep>");
                    print(req, "\t", facts);
                    println("\t<req>");
                    nissues += 1;
                }
            }
        }
        if(nissues > 0) throw "Found <nissues> incomplete triggers"; 
    }
       
    void validateDependencies(){
        availableCalcs = {};
        map[loc,Calculator] calcMap = ();
        dependencies = {};
        for(Calculator calc <- calculators){
            csrcs = calc has src ? [calc.src] : calc.srcs;
            for(src <-  csrcs){
                if(src in calcMap && calcMap[src] != calc){
                   ;//println("Multiple calculators for the same location");
                    //print(calcMap[src], "\t", facts, full=false);
                    //print(calc, "\t", facts, full=false);
                }
                calcMap[src] = calc;
            }
            dependencies += toSet(dependsOn(calc) - csrcs);
        }
        uses = {u.occ | u <- tm.uses};
        xx = tm.defines;
        defs = (xx).defined;
        dependencies += {*req.dependsOn | req <- requirements};
        missing = dependencies - domain(calcMap) - domain(facts) - uses - defs;
        if(!isEmpty(missing)){
            printSolverState();
            throw TypePalUsage("Missing calculators", toList(missing));
        }
    }
    
    // ---- Register triggers
     
    void register(Calculator calc){
        for(dep <- dependsOn(calc)) triggersCalculator[dep] = (triggersCalculator[dep] ? {}) + {calc}; 
    }
    
    void register(Requirement req){
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
        
        for(calc <- triggersCalculator[trigger] ? {} && calc in calculators){  
            evalOrScheduleCalc(calc);
        }
        
        for(req <- triggersRequirement[trigger] ? {} && req in requirements){
            evalOrScheduleReq(req);
        }
        
        for(Use u <- def2uses[trigger] ? {}){
            foundDefs = definedBy[u.occ];
            if({def} := foundDefs, facts[def]?){ 
                openUses -= u;
                addFact(u.occ, facts[def]);
            } else {
                if(all(def <- foundDefs, facts[def]?)){ 
                   openUses -= u;
                   addFact(u.occ, overloadedAType({<def, definitions[def].idRole, instantiate(facts[def])> | loc def <- foundDefs}));
                }
            } 
        }
    }
    
    // ---- Job management ----------------------------------------------------
    void solved(Calculator calc){
        calculators -= calc;
        calculatorJobs -= calc;
    }
    
    void solved(Requirement req){
        requirements -= req;
        requirementJobs -= req;
    }    
    
    // ---- Add a fact --------------------------------------------------------
    
    bool addFact(loc l, AType atype){
        iatype = instantiate(atype);
        facts[l] = iatype;
        if(logSolverSteps)println("!fact <l> ==\> <iatype>");
        fireTrigger(l);
        return true;
    }
    
    // ---- evaluating a Define -----------------------------------------------
    // - amounts to creating a new calculator to compute the defined type
    
    void evalDef(<loc scope, str id, IdRole idRole, loc defined, noDefInfo()>) { }
     
    void evalDef(<loc scope, str id, IdRole idRole, loc defined, defType(value tp)>) {
        if(AType atype := tp){
            if(isFullyInstantiated(atype)){
                facts[defined] = atype;
            } else {
                calculators += calcType(defined, atype);
            }
        } else if(Tree from := tp){
            fromLoc = getLoc(from);
            if(facts[fromLoc]?){
                facts[defined] = facts[fromLoc];
            } else {
                calculators += calcLoc(defined, [fromLoc]);
            }
        }
    }
        
    void evalDef(<loc scope, str id, IdRole idRole, loc defined, defTypeCall(list[loc] dependsOn, AType(Solver tm) getAType)>){
        calculators += calc(id, defined, dependsOn, getAType);
    }
    
    void evalDef(<loc scope, str id, IdRole idRole, loc defined, defTypeLub(list[loc] dependsOn, list[loc] defines, list[AType(Solver tm)] getATypes)>){
        calculators += calcLub(id, defines, dependsOn, getATypes);
    }
    
    list[loc] getDependencies(AType atype){
        deps = [];
        visit(atype){
            case tvar(loc src) : deps += src;
        };
        return deps; 
    }    
    
    // ---- Evaluate/schedule calculators -------------------------------------
    
    void evalOrScheduleCalc(Calculator calc){
        try {
            if(evalCalc(calc)){
                solved(calc);
            } else {
                scheduleCalc(calc);
            }
         } catch checkFailed(list[FailMessage] fmsgs): {
            failMessages += fmsgs;
            solved(calc);
         }
    }
    
    void scheduleCalc(Calculator calc, list[loc] dependsOn){
        if(calc in calculators && calc notin calculatorJobs /*&& calc notin solvedCalculatorJobs*/){
            nAvailable = 0;
            for(dep <- dependsOn) { if(facts[dep]?) nAvailable += 1; }
            enabled = nAvailable == size(dependsOn);
            if(enabled) calculatorJobs += calc;
            if(logSolverSteps){ print(enabled ? "*" : "+"); print(calc, "", facts, full=false); }
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
    
    void scheduleCalc(calc: calcLub(str cnname, list[loc] srcs, list[loc] dependsOn, list[AType(Solver s)] getATypes)){
        scheduleCalc(calc, []);
    }
    
    map[Calculator, int] calculatorAttempts = ();
   
    bool evalCalc(calc: calcType(loc src, AType atype)){
        if(logAttempts) calculatorAttempts[calc] = (calculatorAttempts[calc] ? 0) + 1;
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
        if(logAttempts) calculatorAttempts[calc] = (calculatorAttempts[calc] ? 0) + 1;
        try {
            facts[src] = getType(from);
            if(logSolverSteps)println("!fact <src> ==\> <facts[src]>");
            fireTrigger(src);
            return true;
        } catch TypeUnavailable(): return false; /* cannot yet compute type */
    }
    
    bool evalCalc(calc:calc(str cname, loc src, list[loc] dependsOn,  AType(Solver tm) getAType)){
        if(logAttempts) calculatorAttempts[calc] = (calculatorAttempts[calc] ? 0) + 1;
        if(allDependenciesKnown(dependsOn, calc.eager)){
            try {
                facts[src] = instantiate(getAType(thisSolver));
                bindings2facts(bindings);
                if(logSolverSteps)println("!fact <src> ==\> <facts[src]>");
                fireTrigger(src);
                return true;
            } catch TypeUnavailable(): return false; /* cannot yet compute type */
        }
        return false;
    }
    
    bool evalCalc(calc: calcLub(str cname, list[loc] defines, list[loc] dependsOn, list[AType(Solver tm)] getATypes)){
        if(logAttempts) calculatorAttempts[calc] = (calculatorAttempts[calc] ? 0) + 1;
        known = [];
        solve(known){
            known = [];
            for(getAType <- getATypes){
                try {
                    tp = getAType(thisSolver);
                    // If the type is overloaded pick the one for a variable
                    if(overloadedAType(rel[loc, IdRole, AType] overloads) := tp){
                        for(<loc def, IdRole idRole, AType tp1> <- overloads){
                            if(idRole == variableId()){
                                tp = tp1; break;
                            }
                        }
                    }
                    known += instantiate(tp);
                } catch TypeUnavailable(): /* cannot yet compute type */;
            }
            
            if(size(known) >= 1){
                tp = simplifyLub(known); 
                for(loc def <- defines) { facts[def] = tp; }
                for(loc def <- defines) { fireTrigger(def); }
            }
            if(size(known) == size(getATypes)) {/*println("calcLubsucceeds");*/ return true;}
        }
        return false;
    }
    
    default bool evalCalc(Calculator calc) {
        throw TypePalInternalError("evalCalc cannot handle <calc>");
    }
    
    // ---- evaluate/schedule requirements ------------------------------------
    
     void evalOrScheduleReq(Requirement req){
        try {
            if(allDependenciesKnown(req.dependsOn, req.eager) && evalReq(req)){
                solved(req);  
            } else {
                scheduleReq(req);
            }
        } catch checkFailed(list[FailMessage] fmsgs): {
            failMessages += fmsgs;
            solved(req);
        }
     }
    
    void scheduleReq(Requirement req){
        if(req in requirements && req notin requirementJobs /*&& req notin solvedRequirementJobs*/){
           nAvailable = 0;
           for(dep <- req.dependsOn) { if(facts[dep]?) nAvailable += 1; }
           
           enabled = nAvailable == size(req.dependsOn);
           if(enabled) requirementJobs += req;
           if(logSolverSteps){ print(enabled ? "*" : "+"); print(req, "", facts, full=false); }
       }
    } 
    
    map[Requirement, int] requirementAttempts = ();
    
    bool evalReq(req:reqEqual(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        if(logAttempts) requirementAttempts[req] = (requirementAttempts[req] ? 0) + 1; 
        try {
            if(!_equal(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false; 
    }
    
    bool evalReq(req:reqComparable(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        if(logAttempts) requirementAttempts[req] = (requirementAttempts[req] ? 0) + 1; 
        try {
            if(!_comparable(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
    }
    
    bool evalReq(req:reqSubtype(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        if(logAttempts) requirementAttempts[req] = (requirementAttempts[req] ? 0) + 1; 
        try {
            if(!_subtype(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
    }
    
    bool evalReq(req:reqUnify(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        if(logAttempts) requirementAttempts[req] = (requirementAttempts[req] ? 0) + 1; 
        try {
            if(!_unify(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
    }
    
    bool evalReq(req:reqError(loc src, list[loc] dependsOn, FailMessage fm)){
        if(logAttempts) requirementAttempts[req] = (requirementAttempts[req] ? 0) + 1; 
        failMessages += fm;
        return true;
    }
    
    bool evalReq(req:reqErrors(loc src, list[loc] dependsOn, list[FailMessage] fms)){
        if(logAttempts) requirementAttempts[req] = (requirementAttempts[req] ? 0) + 1; 
        failMessages += fms;
        return true;
    }
    
    bool evalReq(req:req(str rname, loc src,  list[loc] dependsOn, void(Solver s) preds)){
        if(logAttempts) requirementAttempts[req] = (requirementAttempts[req] ? 0) + 1; 
        try {
            preds(thisSolver);
            bindings2facts(bindings);
            solved(req);
        } catch TypeUnavailable(): return false;
        return false;
    }
    
    // Handle bindings resulting from unification
    
    // The binding of a type variable that occurs inside the scope of that type variable can be turned into a fact
    void bindings2facts(map[loc, AType] bindings){
        if(!isEmpty(bindings)){
            for(loc b <- bindings){
               //if(logSolverSteps) println("bindings2facts: <b>, <facts[b]? ? facts[b] : "**undefined**">");
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
    AType getType(value v){
        try {
            switch(v){
                case Tree tree:   return instantiate(findType(tree@\loc));
                case tvar(loc l): return facts[l];
                case AType atype: return instantiate(atype);
                case loc l:       return facts[l];
                case defType(value v) : if(AType atype := v) return atype; else if(Tree tree := v) return instantiate(findType(tree@\loc));
                case Define def:  return getType(def.defInfo);
                case defTypeCall(list[loc] dependsOn, AType(Solver s) getAType):
                    return getAType(thisSolver);
                case defTypeLub(list[loc] dependsOn, list[loc] defines, list[AType(Solver s)] getATypes):
                    return _lubList([getAType(thisSolver) | AType(Solver s) getAType <- getATypes]); //throw "Cannot yet handle defTypeLub in getType";
                default: 
                    throw "getType cannot handle <v>";
            }
        
        } catch NoSuchKey(_):
            throw TypeUnavailable();
        throw "getType cannot return type for <v>";
    }
    
     AType getTypeInScopeFromName0(str name, loc scope, set[IdRole] idRoles){
        u = use(name, anonymousOccurrence, scope, idRoles);
        foundDefs = scopeGraph.lookup(u);
        if({def} := foundDefs){
            return instantiate(facts[def]);
        } else {
          if(mayOverloadFun(foundDefs, definitions)){
            overloads = {<d, idRole, instantiate(facts[d])> | loc d <- foundDefs, IdRole idRole := definitions[d].idRole, idRole in idRoles};
            return overloadedAType(overloads);
          } else {
             _reports([error(d, "Double declaration of %q in %v", name, foundDefs) | d <- foundDefs] /*+ error("Undefined `<id>` due to double declaration", u.occ) */);
          }
        }
        throw TypeUnavailable();
    }
    
    //@memo
    AType _getTypeInScopeFromName(str name, loc scope, set[IdRole] idRoles){
        try {
            return getTypeInScopeFromName0(name, scope, idRoles);
        } catch NoSuchKey(value k):
                throw TypeUnavailable();
        //catch NoBinding():
        //        throw TypeUnavailable();
    }
    
    AType getTypeInScope0(Tree occ, loc scope, set[IdRole] idRoles){
        //println("getTypeInScope0: <occ>, <scope>, <idRoles>");
        id = unescapeName("<occ>");
        u = use(unescapeName("<occ>"), getLoc(occ), scope, idRoles);
        //println("u: <u>");
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
             _reports([error(d, "Double declaration of %q in %v", id, foundDefs) | d <- foundDefs] /*+ error("Undefined `<id>` due to double declaration", u.occ) */);
          }
        }
        throw TypeUnavailable();
    }
    
    //@memo
    AType _getTypeInScope(Tree occ, loc scope, set[IdRole] idRoles){
        try {
            return getTypeInScope0(occ, scope, idRoles);
        } catch NoSuchKey(_):
                throw TypeUnavailable();
        //catch NoBinding():
        //        throw TypeUnavailable();
    }
    
    void addUse(set[loc] defs, Use u){
        for(loc def <- defs){
            if(definedBy[u.occ]?){
                definedBy[u.occ]  = { isContainedIn(def, d) ? def : d | loc d <- definedBy[u.occ] };
            } else {
                definedBy[u.occ] = {def};
            }
            if(def2uses[def]?){
                def2uses[def] += {u};
            } else {
                def2uses[def] = {u};
            }
        }  
    }
      
    AType _getTypeInType(AType containerType, Tree selector, set[IdRole] idRolesSel, loc scope){
       // println("getTypeInType: <containerType>, <selector>, <idRolesSel>");
       
        selectorLoc = getLoc(selector);
        selectorName = unescapeName("<selector>");
       
        selectorUse = use(selectorName, selectorLoc, scope, idRolesSel);
        if(overloadedAType(rel[loc, IdRole, AType] overloads) := containerType){
            rel[loc, IdRole, AType]  valid_overloads = {};
            for(<key, role, tp> <- overloads){
                try {
                    selectorType = _getTypeInType(tp, selector, idRolesSel, scope);
                    //selectorType = getTypeInNamelessTypeFun(tp, selector, scope, thisSolver);
                    valid_overloads += <key, role, selectorType>;
                } catch checkFailed(list[FailMessage] _): ; // do nothing and try next overload
                  catch NoBinding(): ; // do nothing and try next overload
//>>              catch e: 
            }
            if(isEmpty(valid_overloads)){
                _report(error(selector, "getTypeInType: Cannot access fields on type %t", containerType));
            } else if({<loc key, IdRole role, AType tp>} := valid_overloads){
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
            //unavailable = false;
            
            int i = 0;
            some_accessible_def = false;
            while(i < ncontainerNames){
                containerName = containerNames[i];
                i += 1;
                all_definitions = getDefinitions(containerName, scope, containerRoles);
                some_accessible_def = some_accessible_def || !isEmpty(all_definitions);
                for(containerDef <- all_definitions){    
                    try {
                        selectorType = getTypeInScope0(selector, containerDef.defined, idRolesSel);
                        valid_overloads += <containerDef.defined, containerDef.idRole, instantiateTypeParameters(selector, getType(containerDef.defInfo), containerType, selectorType, thisSolver)>;
                     } //catch TypeUnavailable():
                            //unavailable = true;
                       catch NoSuchKey(_):
                            ;//navailable = true;
                       catch NoBinding(): {
                            try {
                                selectorType = getTypeInTypeFromDefineFun(containerDef, selectorName, idRolesSel, thisSolver);
                                valid_overloads += <containerDef.defined, containerDef.idRole, instantiateTypeParameters(selector, getType(containerDef.defInfo), containerType, selectorType, thisSolver)>;
                            } //catch TypeUnavailable():
                              //  unavailable = true;
                              catch NoBinding():
                                ;//unavailable = true;
                               // _report(error(selector, "No definition for %v %q in type %t", intercalateOr([replaceAll(getName(idRole), "Id", "") | idRole <- idRolesSel]), "<selector>", containerType));
                        }
                 }
                 /*if(unavailable) throw TypeUnavailable();*/
                 if(isEmpty(valid_overloads)){
                    /*if(unavailable) throw TypeUnavailable();*/
                     if(i == ncontainerNames){
                        if(some_accessible_def)
                            _report(error(selector, "No definition found for %v %q in type %t", intercalateOr([prettyRole(idRole) | idRole <- idRolesSel]), "<selector>", containerType));
                        else
                            _report(error(selector, "No definition for type %t is available here", containerType));
                     }
                  } else if({<loc key, IdRole role, AType tp>} := valid_overloads){
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
                _report(error(selector, "No definition for %q in type %t", "<selector>", containerType));
            }
         }
        throw checkFailed([error(selector, "getTypeInType")]);
    }
     
    rel[str id, AType atype] _getAllDefinedInType(AType containerType, loc scope, set[IdRole] idRoles){
        <containerNames, containerRoles> = getTypeNamesAndRole(containerType);
        if(!isEmpty(containerNames)){
            containerName = containerNames[0];
            results = {};
            try {
                for(containerDef <- getDefinitions(containerName, scope, containerRoles)){   
                    results += { <id, getType(defInfo)> |  <str id, IdRole idRole, loc defined, DefInfo defInfo> <- defines[containerDef.defined] ? {}, idRole in idRoles };
                }
                return results;
             } catch AmbiguousDefinition(set[loc] foundDefs): {               //if(!mayOverloadFun(foundDefs, definitions)){
                messages += [error("Double declaration of `<definitions[defined].id>`", defined) | defined  <- foundDefs];
                return results;
             }      
         } else {
            throw TypePalUsage("`getAllDefinedInType` is only defined on a named type, found `<prettyAType(containerType)>`");
         }
    }
    
    set[Define] getDefinitions(str id, loc scope, set[IdRole] idRoles){
        try {
            foundDefs = scopeGraph.lookup(use(id, anonymousOccurrence, scope, idRoles));
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
                //println("getDefinitions: <id> in scope <scope> <idRoles> ==\> TypeUnavailable2");
                //throw TypeUnavailable(); // <<<<
                return {};
           }
    }
    
    set[Define] getDefinitions(Tree tree, set[IdRole] idRoles)
        = getDefinitions(getLoc(tree), idRoles);
    
    set[Define] getDefinitions(loc scope, set[IdRole] idRoles)
        = {<scope, id, idRole, defined, defInfo> | <str id, IdRole idRole, loc defined, DefInfo defInfo> <- tm.defines[scope], idRole in idRoles };
        
    set[Define] getAllDefines() = tm.defines;
    
    Define getDefine(loc l) = definitions[l];
    
    // ---- resolvePath -------------------------------------------------------
    
    bool resolvePaths(){
        newPaths = {};
        referPaths = tm.referPaths;
        for(ReferPath rp <- referPaths){
            try {
                if(referToDef(Use use, PathRole pathRole) := rp){
                    u = rp.use;
                    foundDefs = scopeGraph.lookup(u);
                    if({loc def} := foundDefs){
                       definedBy[u.occ] = foundDefs;
                       newPaths += {<u.scope, rp.pathRole, def>};  
                    } else {
                        messages += error("Name `<u.id>` is ambiguous <foundDefs>", u.occ);
                    }
                    referPaths -= {rp}; 
                } else {
                    containerType = getType(rp.occ);
                    <containerNames, containerRoles> = getTypeNamesAndRole(containerType);
                    ncontainerNames = size(containerNames);
                    if(ncontainerNames > 0){
                        set[loc] found_scopes = {};
                        
                        int i = 0;
                        some_accessible_def = false;
                        while(i < ncontainerNames){
                            containerName = containerNames[i];
                            i += 1;
                            all_definitions = getDefinitions(containerName, rp.scope, containerRoles);
                            found_scopes = {containerDef.defined | containerDef <- all_definitions};
                            
                             if(isEmpty(found_scopes)){
                                 if(i == ncontainerNames){
                                    _report(error(rp.occ, "No definition found for type %t", containerType));
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
                ;//println("Lookup/getType for <rp> fails"); 
                /* ignore until end */
             }
        }
        tm.paths += newPaths;
        tm.referPaths = referPaths;
        return !isEmpty(newPaths);
    }
    
    // ---- "equal" and "requireEqual" ----------------------------------------
       
    bool _equal(AType given, AType expected){
        if(given == expected) return true;
        if(isFullyInstantiated(given)){
             if(isFullyInstantiated(expected)){
                return instantiate(unsetRec(given)) == instantiate(unsetRec(expected));
             } else
                 throw TypeUnavailable();
        } else
            throw TypeUnavailable();
    }
    
    bool _equal(Tree given, AType expected) = _equal(getType(given), expected);
    
    bool _equal(AType given, Tree expected) = _equal(given, getType(expected));
    
    bool _equal(Tree given, Tree expected) = _equal(getType(given), getType(expected));
    
    default bool _equal(value given, value expected) { throw TypePalUsage("`equal` called with <given> and <expected>"); }
    
    void _requireEqual(value given, value expected, FailMessage fm) {
        if(!_equal(given, expected)) _report(fm);
    }
   
    // ---- "unify" and "requireUnify" ----------------------------------------
    
    bool _unify(AType given, AType expected) = unify(given, expected);
    
    bool _unify(Tree given, AType expected) = unify(getType(given), expected);
    
    bool _unify(AType given, Tree expected) = unify(given, getType(expected));
    
    bool _unify(Tree given, Tree expected) = unify(getType(given), getType(expected));
    
    default bool _unify(value given, value expected) { throw TypePalUsage("`_unify` called with <given> and <expected>"); }
    
    bool _unify(value given, value expected, FailMessage fm) {
        return unify(given, expected) || _report(fm);
    }
    
    void _requireUnify(value given, value expected, FailMessage fm){
        if(!_unify(given, expected)) _report(fm);
    }
    
    bool unify(AType given, AType expected){
        <ok, bindings1> = unify(given, expected, bindings);
        if(logSolverSteps)println("unify(<given>, <expected>) ==\> <ok>, <bindings1>");
        if(ok){
            bindings += bindings1;
            return true;
        } else {
            return false;
        }
    }
    
    // Unification of two types, for now, without checks on variables
    tuple[bool, map[loc, AType]] unify(AType t1, AType t2, map[loc, AType] bindings){
        //println("unify: <t1>, <t2>");
        if(t1 == t2) return <true, bindings>;
       
        if(tvar(loc tv1) := t1){
        
            try {
                t11 = findType(tv1);
                if(t11 != t1){
                    if(tm.config.isSubType? && _subtype(t11, t1)) 
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
                   if(tm.config.isSubType? && _subtype(t21, t2)) 
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
    
     AType _instantiate(AType atype) = instantiate(atype);
    
    // ---- "subtype" and "requireSubType" ------------------------------------
     
    bool _subtype(Tree given, AType expected) = _subtype(getType(given), expected);
    
    bool _subtype(AType given, Tree expected) = _subtype(given, getType(expected));
    
    bool _subtype(Tree given, Tree expected) = _subtype(getType(given), getType(expected));
    
    default bool _subtype(value given, value expected) { throw TypePalUsage("`subtype` called with <given> and <expected>"); }
    
    bool _subtype(AType small, AType large){
        if(isFullyInstantiated(small)){
            if(isFullyInstantiated(large)){
                return isSubTypeFun(small, large);
            } else  
                throw TypeUnavailable();
        } else {
          throw TypeUnavailable();
        }
    }
    
    void _requireSubType(value given, value expected, FailMessage fm){
        if(!_subtype(given, expected)) _report(fm);
    }
    
    // ---- "comparable" and "requireComparable" ------------------------------
    
    bool _comparable(Tree given, AType expected) = _comparable(getType(given), expected);
    
    bool _comparable(AType given, Tree expected) = _comparable(given, getType(expected));
    
    bool _comparable(Tree given, Tree expected) = _comparable(getType(given), getType(expected));
    
    default bool _comparable(value given, value expected) { throw TypePalUsage("`comparable` called with <given> and <expected>"); }
    
    bool _comparable(AType atype1, AType atype2){
        if(atype1 == atype2) return true;
        if(isFullyInstantiated(atype1) && isFullyInstantiated(atype2)){
            return isSubTypeFun(atype1, atype2) || isSubTypeFun(atype2, atype1);
        } else {
            throw TypeUnavailable();
        }
    }
    
    void _requireComparable(value given, value expected, FailMessage fm){
        if(!_comparable(given, expected)) _report(fm);
    }
    
    // ---- requireTrue and requireFalse --------------------------------------
    
    void _requireTrue(bool b, FailMessage fm){
        if(!b) _report(fm);
    }
    
    void _requireFalse(bool b, FailMessage fm){
        if(b) _report(fm);
    }
    
    // ---- lubList -----------------------------------------------------------
    
    AType _lubList(list[AType] atypes) = simplifyLub(atypes);
     
    // ---- lub ---------------------------------------------------------------
    
    AType _lub(Tree given, AType expected) = _lub(getType(given), expected);
    
    AType _lub(AType given, Tree expected) = _lub(given, getType(expected));
    
    AType _lub(Tree given, Tree expected) = _lub(getType(given), getType(expected));
    
    AType _lub(AType t1, AType t2) = simplifyLub([t1, t2]);
    
    default AType _lub(value given, value expected) { throw TypePalUsage("`lub` called with <given> and <expected>"); }
    
    AType simplifyLub(list[AType] atypes) {
        //println("simplifyLub: <atypes>");
        lubbedType = theMinAType;
        other = [];
        for(AType t <- atypes){
            if(isFullyInstantiated(t)){
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
                //println("add <b>, <bindings[b]>");
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
        //println("simplifyLub: <atypes> ==\> <res>");
        return res;
    }
    
    // ---- The "fact" assertion ----------------------------------------------
    
    void fact(value v, AType atype){
        if(Tree t := v) {
            addFact(getLoc(t), atype);
         } else if(loc l := v){
            addFact(l, atype);
         } else {
            throw TypePalUsage("First argument of `fact` should be `Tree` or `loc`, found `<typeOf(v)>`");
         }
    }
    
    void specializedFact(value v, AType atype){
        if(Tree t := v) {
            specializedFacts[getLoc(t)] = atype;
         } else if(loc l := v){
            specializedFacts[l] = atype;
         } else {
            throw TypePalUsage("First argument of `specializedFact` should be `Tree` or `loc`, found `<typeOf(v)>`");
         }
    }

    bool allDependenciesKnown(set[loc] deps, bool eager)
        = isEmpty(deps) || (eager ? all(dep <- deps, facts[dep]?)
                                  : all(dep <- deps, facts[dep]?, isFullyInstantiated(facts[dep])));
    
    bool allDependenciesKnown(list[loc] deps, bool eager)
        = isEmpty(deps) || (eager ? all(dep <- deps, facts[dep]?)
                                  : all(dep <- deps, facts[dep]?, isFullyInstantiated(facts[dep])));
    
    bool isFullyInstantiated(AType atype){
        visit(atype){
            case tvar(loc tname): { if(!facts[tname]?) return false;
                                    if(tvar(tname2) := facts[tname]) return false;
                                  }
            case lazyLub(list[AType] atypes): if(!(isEmpty(atypes) || all(AType tp <- atype, isFullyInstantiated(tp)))) return false;
            case overloadedAType(rel[loc, IdRole, AType] overloads): all(<k, idr, tp> <- overloads, isFullyInstantiated(tp));
        }
        return true;
    }
   
    // Find a (possibly indirectly defined) type for src
    AType findType(loc src){
        if(bindings[src]?){
            v = bindings[src];
            if(tvar(loc src1) := v && src1 != src && (bindings[src1]? || facts[src1]?)) return findType(src1);
            return v;
        }
        if(facts[src]?){
            v = facts[src];
            if(tvar(loc src1) := v && src1 != src && (bindings[src1]? || facts[src1]?)) return findType(src1);
            return v;
        }
       throw NoSuchKey(src);
    }
    
    // Substitute a type variable first using bindings, then facts; return as is when there is no binding
    AType substitute(tv: tvar(loc src)){
        if(bindings[src]?) { b = bindings[src]; return b == tv ? tv : substitute(b); }
        if(facts[src]?) { b = facts[src]; return b == tv ? tv : substitute(b); }
        return tv;
    }
    
    default AType substitute(AType atype){
            return atype;
    }
    
    // Recursively instantiate all type variables and lazyLubs in a type
    AType instantiate(AType atype){
      return
          visit(atype){
            case tv: tvar(_) => substitute(tv)
            case lazyLub(list[AType] atypes) : {
                list[AType] sbs = [substitute(tp) | AType tp <- atypes];
                insert simplifyLub(sbs);
                }
          };
    }
        
    /*
     *  run: validates an extracted TModel via constraint solving
     *  
     */
    TModel _run(){
    
        int runStarted = cpuTime();
        
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
        
        println("checking <tm.modelName>");
           
        if(logSolverIterations) println("<tm.modelName>, initial -- calculators: <size(calculators)>; requirements: <size(requirements)>; uses: <size(tm.uses)>; facts: <size(facts)>");
             
        if(logSolverSteps) printTModel(tm);
        
        validateDependencies();
        
        resolvePaths();
       
        // Check that all uses have a definition and that all overloading is allowed
        if(logSolverSteps) println("..... lookup <size(tm.uses)> uses");
        int now = cpuTime();
         
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
                  if(logSolverSteps) println("!use  \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <foundDefs>");
                } else {
                    messages += [error("Double declaration of `<getId(u)>`", d) | d <- foundDefs] + error("Undefined `<getId(u)>` due to double declaration", u.occ);
                    if(logSolverSteps) println("!use  \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** double declaration **");
                }
            }
            catch NoBinding(): {
                notYetDefinedUses += u;
            }
            catch TypeUnavailable(): {
                notYetDefinedUses += u;
            }
        }
        int initCheckUsesTime = cpuTime() - now;
        
        // Check for illegal overloading of unused definitions
        set[loc] unusedDefs = domain(definitions) - actuallyUsedDefs;
        if(logSolverSteps) println("..... filter doubles in <size(unusedDefs)> unused defines");
        now = cpuTime();
        
        for(ud <- unusedDefs){
            udef = definitions[ud];
            scope = udef.scope;
            id = udef.id;
            idRole = udef.idRole;
            defined = udef.defined;
        
            u = use(id, defined, scope, {idRole}); // turn each unused definition into a use and check for double declarations;
            try {
               foundDefs = scopeGraph.lookup(u);
               foundDefs = { fd | fd <- foundDefs, definitions[fd].idRole in u.idRoles };
               if(isEmpty(foundDefs)){
                    throw TypePalInternalError("No binding found while checking for double definitions"); 
               } else 
               if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                 ;
                } else {
                    messages += [error("Double declaration of `<getId(u)>`", d) | d <- foundDefs] + error("Undefined `<getId(u)>` due to double declaration", u.occ);
                    if(logSolverSteps) println("!use  \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** double declaration **");
                }
            }
            catch NoBinding(): {
                throw TypePalInternalError("No binding found while checking for double definitions"); 
            }  
        }
        
        unusedDefs = actuallyUsedDefs = {};
      
        int initFilterDoublesTime = cpuTime() - now;
        
        // Process all defines (which may create new calculators/facts)
        
        now = cpuTime();
        if(logSolverSteps) println("..... handle <size(defines)> defines");
        for(Define def <- defines){
            try {
                //if(def.defined notin def2uses && reportUnused(def.defined, tm.definitions, tm.scopes, tm.facts, tm.config)){ 
                //    messages += warning("Unused <prettyRole(def.idRole)> `<def.id>`", def.defined); 
                //}
                evalDef(def);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
            }
        }
        int initDefTime = cpuTime() - now;
        
        // Register all dependencies
        
        now = cpuTime();
        for(Calculator calc <- calculators){
            register(calc);
        }
        
        for(Requirement req <- requirements){
            register(req);
        }
        
        //validateTriggers();
        
        int initRegisterTime = cpuTime() - now;
       
        // See what the facts derived sofar can trigger
        now = cpuTime();
        for(fct <- facts){
            try {
                fireTrigger(fct);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
            }
        }

        int initFactTriggerTime = cpuTime() - now;
        
        // Try to evaluate or schedule the calculators
        now = cpuTime();
        if(logSolverSteps) println("..... handle <size(calculators)> calculators");
 
        for(Calculator calc <- calculators){
            try {
            	clearActiveTriggers();
                evalOrScheduleCalc(calc);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
            }
        }
        int initCalcTime = cpuTime() - now;
        
        // Try to evaluate or schedule the requirements
        now = cpuTime();
        if(logSolverSteps) println("..... handle <size(requirements)> requirement");
        for(Requirement req <- requirements){
            try {
                clearActiveTriggers(); // ? needed
                evalOrScheduleReq(req);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
             }
        }
        int initReqTime = cpuTime() - now;
        
        // Here we have jobs for calculators and requirements with known dependencies
      
        int mainStarted = cpuTime();
        int mainCalcTime = 0;
        int mainReqTime = 0;
        
        /****************** main solve loop *********************************/
        
        if(logSolverSteps) println("..... start solving");
        
        int iterations = 0;
        int ncalculators = size(calculators);
        int nrequirements = size(requirements);
        int nfacts = size(facts);
        int nopenUses = size(openUses);
        int nreferPaths = size(referPaths);
        
        solve(nreferPaths, ncalculators, nrequirements, nfacts, nopenUses){ 
            iterations += 1;
            if(logSolverIterations){
                println("<tm.modelName>, iter #<iterations> -- calculators: <ncalculators>; calculatorJobs: <size(calculatorJobs)>; requirements: <nrequirements>; requirementJobs: <size(requirementJobs)>; uses: <size(openUses)>; referPaths: <nreferPaths>; facts: <size(facts)>; ");
            }
            
            // ---- referPaths
            
            resolvePaths();
            
            for(u <- notYetDefinedUses){
                try {
                   foundDefs = scopeGraph.lookup(u);
                   foundDefs = { fd | fd <- foundDefs, definitions[fd].idRole in u.idRoles };
                   if(isEmpty(foundDefs)){
                        throw NoBinding();
                   } else 
                   if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                      definedBy[u.occ] = foundDefs;
                      for(def <- foundDefs) def2uses[def] = (def2uses[def] ? {}) + u;
                      openUses += u;
                      notYetDefinedUses -= u;
                     
                      if(logSolverSteps) println("!use  \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <foundDefs>");
                      
                      if({def} := foundDefs, facts[def]?){ 
                        openUses -= u;
                        addFact(u.occ, facts[def]);
                      } else {
                        if(all(def <- foundDefs, facts[def]?)){ 
                            openUses -= u;
                            addFact(u.occ, overloadedAType({<def, definitions[def].idRole, instantiate(facts[def])> | loc def <- foundDefs}));
                        }
                      } 
                    } else {
                        messages += [error("Double declaration of `<getId(u)>`", d) | d <- foundDefs] + error("Undefined `<getId(u)>` due to double declaration", u.occ);
                        if(logSolverSteps) println("!use  \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** double declaration **");
                    }
                } catch NoBinding(): {
                    ; //ignore until end
                } catch TypeUnavailable() : {
                    ; // ignore until end
                }
            }
            
                
            // ---- calculatorJobs
           
            now = cpuTime();
            for(Calculator calc <- calculatorJobs){
                 try {
                 	clearActiveTriggers();
                    if(evalCalc(calc)){
                       solved(calc);
                    } else {
                        if(logSolverSteps){ print("?"); print(calc, "", facts, full=false); }
                    }
                 } catch checkFailed(list[FailMessage] fms): {
                        failMessages += fms;
                        solved(calc);
                 }
            } 
            mainCalcTime += cpuTime() - now;
           
            // ---- requirementJobs
            
            now = cpuTime();
            for(Requirement req <- requirementJobs){
                try {
                    clearActiveTriggers(); // ? needed
                    if(evalReq(req)){
                        solved(req);
                    } else {
                        if(logSolverSteps){ print("?"); print(req, "", facts, full=false); }
                    }
                } catch checkFailed(list[FailMessage] fms): {
                    failMessages += fms;
                    solved(req);
                }
            }
            mainReqTime += cpuTime() - now;
             
            ncalculators = size(calculators);
            nrequirements = size(requirements);
            nfacts = size(facts);
            nopenUses = size(openUses);
            nreferPaths = size(referPaths);
        }
           
        /****************** end of main solve loop *****************************/
           
        int mainEnded = cpuTime();
           
        if(logSolverSteps) println("..... solving complete");
           
        tm.config.postSolver(namedTrees, thisSolver);
        
        int postSolverTime = cpuTime() - mainEnded;
        
        // Convert all FaillMessages into Messages
        for(fm <- failMessages){
            messages += toMessage(fm, getType);
        }
        
        for(Use u <- openUses){
            try {
                 foundDefs = scopeGraph.lookup(u);
             } catch NoBinding(): {
                roles = size(u.idRoles) > 5 ? "" : intercalateOr([prettyRole(idRole) | idRole <- u.idRoles]);
                messages += error("Undefined <roles> `<getId(u)>`", u.occ);
             }
        }
        
        for(u <- notYetDefinedUses){
            roles = size(u.idRoles) > 5 ? "" : intercalateOr([prettyRole(idRole) | idRole <- u.idRoles]);
            messages += error("Undefined <roles> `<getId(u)>`", u.occ);
        }
         
        
        for(rp <- referPaths){
            switch(rp){
            case referToDef(u, pathRole):
                messages += error("Reference to name `<rp.use.id>` cannot be resolved", rp.use.occ);
            case referToType(occ, currentScope, pathRole):
                messages += error("Reference to type definition cannot be resolved", occ);
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
                for(def <- foundDefs, !facts[u.occ]?, !alreadyReported(messages, u.occ)) {
                    messages += error("Unresolved type for `<u has id ? u.id : u.ids>`", u.occ);
                }
            }
            
            calcNoLubs = [calc | calc <- calculators, !(calc is calcLub)];
          
            for(Calculator clc <- sort(calcNoLubs, bool(Calculator a, Calculator b){ return a.src.length < b.src.length; })){
                src = clc.src;
                if(!facts[src]?, !alreadyReported(messages, src)){
                    set[loc] cdeps = toSet(dependsOn(clc));
                    if(!facts[src]? && isEmpty(reportedLocations & cdeps)){
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
                    if(!facts[src]? && isEmpty(reportedLocations & cdeps)){
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
        
        if(logAttempts){
            lrel[Calculator, int] sortedCalcFreqs = sort(toList(calculatorAttempts), bool(tuple[Calculator calc, int freq] a, tuple[Calculator calc, int freq] b) { return a.freq > b.freq; });
            int ncalc = 0;
            for(<clc, freq> <- sortedCalcFreqs, ncalc < 10){
               print("<freq>:"); print(clc, "\t", facts);
               ncalc += 1;
            }
            sortedReqFreqs = sort(toList(requirementAttempts), bool(tuple[Requirement req, int freq] a, tuple[Requirement req, int freq] b) { return a.freq > b.freq; });
            int nreq = 0;
            for(<rq, freq> <- sortedReqFreqs, nreq < 10){
               print("<freq>:"); print(rq, "\t", facts);
               nreq += 1;
            }
        }
       
        if(logSolverIterations){
            println("iterations: <iterations>; calculators: <ncalculators>; calculatorJobs: <size(calculatorJobs)>; requirements: <nrequirements>; requirementJobs: <size(requirementJobs)>; uses: <size(openUses)>; referPaths: <nreferPaths>; facts: <size(facts)>; ");
         }
         if(logTModel){
            printSolverState();
            printDef2uses();
            printUse2Def();
            if(isEmpty(messages) && isEmpty(requirements) && isEmpty(calculators)){
                println("No type errors found");
             } else {
                println("Errors:");
                for(msg <- messages){
                    println(msg);
                }
                if(!isEmpty(requirements)) println("*** <size(requirements)> unresolved requirements ***");
                if(!isEmpty(calculators)) println("*** <size(calculators)> unresolved calculators ***");
             }
          }
          
          tm.calculators = calculators;
          tm.requirements = requirements;
 
          tm.facts = facts;
         // prune the definedBy relation using specialized facts
          for(loc u <- specializedFacts){
            orgtp = facts[u];
            spectp = specializedFacts[u];
            if(definedBy[u]? && overloadedAType(org_overloads) := orgtp){
                //println("definedBy[<u>] before: <definedBy[u]>");
                if(overloadedAType(spec_overloads) := spectp){
                    definedBy[u] = { def | <def, idRole, otype> <- org_overloads, otype in spec_overloads<2>};
                } else {
                    definedBy[u] = { def | <def, idRole, otype> <- org_overloads, otype == spectp};
                }
                //println("definedBy[<u>] after: <definedBy[u]>");
            }
          }
          
          tm.specializedFacts = specializedFacts;
          tm.useDef = { *{<u, d> | loc d <- definedBy[u]} | loc u <- definedBy };
          
          ldefines = for(tup: <loc scope, str id, IdRole idRole, loc defined, DefInfo defInfo> <- tm.defines){
                            if((defInfo has getAType || defInfo has getATypes)){
                                       try {                   
                                           dt = defType(tm.facts[defined]);
                                           tup.defInfo = setKeywordParameters(dt, getKeywordParameters(defInfo));
                                           
                                       } catch NoSuchKey(k): {
                                         continue;
                                       }
                                    } 
                                    append tup;
                          };
          tm.defines = toSet(ldefines);
                          
          for(Define def <- tm.defines){
                if(def.defined notin def2uses && reportUnused(def.defined, tm)){ 
                    messages += warning("Unused <prettyRole(def.idRole)> `<def.id>`", def.defined); 
                }
           }
          
          tm.messages = sortMostPrecise(toList(toSet(messages)));
         
          if(logSolverSteps) println("Derived facts: <size(tm.facts)>");
          solverEnded = cpuTime();
          M = 1000000;
          if(logTime){
            println("<tm.modelName>, solver total: <(solverEnded - solverStarted)/M> ms; init: <(mainStarted - runStarted)/M> ms [ doubles <initFilterDoublesTime/M>; uses <initCheckUsesTime/M>; def <initDefTime/M>; register <initRegisterTime/M>; fact triggers <initFactTriggerTime/M>; calc <initCalcTime/M>; req <initReqTime/M> ]; run main loop: <(mainEnded - mainStarted)/M> ms [ calc <mainCalcTime/M>; req <mainReqTime/M> ]; finish: <(solverEnded - mainEnded)/M> ms [ postSolver <postSolverTime/M> ]");
          }
          return tm;
    }
    
    // The actual code of newSolver
    
    Solver thisSolver = 
            solver(
            /* Lifecycle */     _run,
            /* Types */         getType, 
                                _getTypeInScope,
                                _getTypeInScopeFromName,
                                _getTypeInType,
                                _getAllDefinedInType,
           /*Fact */            fact,
                                specializedFact,
          /* Calculate & Require */ 
                                _equal,
                                _requireEqual,
                                _unify,
                                _requireUnify,
                                _comparable,
                                _requireComparable,
                                _subtype,
                                _requireSubType,
                                _lub,
                                _lubList,
                                _requireTrue,
                                _requireFalse,
           /* Inference */      _instantiate,
                                isFullyInstantiated,
           /* Reporting */      _report,
                                _reports,
                                _addMessages,
                                _reportedErrors,
           /* Global Info */    _getConfig,
                                _getFacts,
                                _getPaths,
                                _getStore,
                                _putStore,
                                getDefinitions,
                                getAllDefines,
                                getDefine
                     );
                     
    ScopeGraph scopeGraph = newScopeGraph(tm, tm.config, thisSolver);
    return thisSolver;
}
