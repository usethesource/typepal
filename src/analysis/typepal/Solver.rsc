module analysis::typepal::Solver

import Set; 
import Node;
import Map;
import IO;
import List; 
import ParseTree;
import String;
import Message;
import Exception;
import util::Benchmark;

extend analysis::typepal::AType;
extend analysis::typepal::Collector;
extend analysis::typepal::FailMessage;
extend analysis::typepal::Messenger;
extend analysis::typepal::ScopeGraph;
extend analysis::typepal::TypePalConfig;
extend analysis::typepal::Utils;


// The Solver data type: a collection of call backs

data Solver
    = solver(
        AType(value) getType,
        AType (str id, loc scope, set[IdRole] idRoles) getTypeInScope,
        AType (AType containerType, Tree selector, set[IdRole] idRolesSel, loc scope) getTypeInType,
        rel[str id, AType atype] (AType containerType, loc scope, set[IdRole] idRoles) getAllDefinedInType,
        
        bool (value, value) equal,
        void (value, value, FailMessage) requireEqual,
       
        bool (value, value) unify,
        void (value, value, FailMessage) requireUnify,
        
        bool (value, value) comparable,
        void (value, value, FailMessage) requireComparable,
        
        void (bool, FailMessage) requireTrue,
        void (bool, FailMessage) requireFalse,
        
        AType (AType) instantiate,
        bool (AType atype) isFullyInstantiated,
        void (value, AType) fact,
        
        bool (value, value) subtype,
        void (value, value, FailMessage) requireSubtype,
        
        AType (value, value) lub,
        AType (list[AType]) lubList,
        TModel () run,
        bool(FailMessage fm) report,
        bool (list[FailMessage]) reports,
        TypePalConfig () getConfig,
        map[loc, AType]() getFacts,
        map[str,value]() getStore,
        set[Define] (str id, loc scope, set[IdRole] idRoles) getDefinitions    // deprecated
    );
    
Solver newSolver(Tree tree, TModel tm){
    
    // Configuration (and related state)
    
    bool cdebug = tm.debug;
    bool verbose = tm.verbose;
    int solverStarted = cpuTime();
    
    str(str) unescapeName  = defaultUnescapeName;
    bool(AType,AType) isSubTypeFun = defaultIsSubType;
    
    AType(AType,AType) getLubFun = defaultGetLub;
    
    AType theMinAType = atypeList([]);
    AType theMaxAType = atypeList([]);
    
    bool defaultMayOverload(set[loc] defs, map[loc, Define] defines) = false;
    
    bool (set[loc] defs, map[loc, Define] defines) mayOverloadFun = defaultMayOverload;
    
    set[loc] (TModel, Use) lookupFun = lookup;
    
    AType (Tree subject, AType def, AType ins, AType act, Solver s) instantiateTypeParameters = defaultInstantiateTypeParameters;
    
    tuple[bool isNamedType, str typeName, set[IdRole] idRoles] (AType atype) getTypeNameAndRole = defaultGetTypeNameAndRole;
    
    AType (Define containerDef, str selectorName, set[IdRole] idRolesSel, Solver s) getTypeInTypeFromDefineFun = defaultGetTypeInTypeFromDefine;
    
    AType(AType containerType, Tree selector, loc scope, Solver s) getTypeInNamelessTypeFun = defaultGetTypeInNamelessType;
    
    void configTypePal(TypePalConfig tc){
        configScopeGraph(tc);
        
        unescapeName = tc.unescapeName;
        isSubTypeFun = tc.isSubType;
        getLubFun = tc.getLub;
        mayOverloadFun = tc.mayOverload;
        lookupFun = tc.lookup;       
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
        
        //getMinATypeFun = tc.getMinAType;
        //getMaxATypeFun = tc.getMaxAType;
        instantiateTypeParameters = tc.instantiateTypeParameters;
        getTypeNameAndRole = tc.getTypeNameAndRole;
        getTypeInTypeFromDefineFun = tc.getTypeInTypeFromDefine;
        getTypeInNamelessTypeFun = tc.getTypeInNamelessType;
    }
    
    TypePalConfig _getConfig() = tm.config;
    
    map[loc, AType] _getFacts() = facts;
    
    map[str, value] _getStore() = tm.store;
    
    // State of Solver
    
    map[loc, AType] facts = ();
    
    set[Define] defines = {};
    
    map[loc, Define] definitions = ();
    
    set[Calculator] calculators = tm.calculators;
    set[Calculator] calculatorJobs = {};
    set[Calculator] solvedCalculatorJobs = {};
    map[loc, set[Calculator]] triggersCalculator = ();
     
    set[Requirement] requirements = tm.requirements;
    set[Requirement] requirementJobs = {};
    set[Requirement] solvedRequirementJobs = {};
    map[loc, set[Requirement]] triggersRequirement = ();
    
    set[loc] activeTriggers = {};
    
    map[loc, set[Use]] def2uses = ();
    map[loc, set[loc]] definedBy = ();
    set[Use] openUses = {};
    
    map[loc, AType] bindings = ();
    list[Message] messages = [];
    list[FailMessage] failMessages = [];
    
    // ---- printing
    
    void printSolverState(){
        println("\nDERIVED FACTS");
            for(loc fact <- facts){
                println("\t<fact>: <facts[fact]>");
            }
        if(size(requirements) + size(calculators)  + size(openUses) > 0){
            println("\nUNRESOLVED");
          
            for(req <- requirements){
                print(req in requirementJobs ? "*" : " ");
                print(req, "\t", facts);
            }
            
            for(calc <- calculators){
                print(calc in calculatorJobs ? "*" : " ");
                print(calc, "\t", facts);
            }
            
            for(u <- openUses){
                println("\t<u>");
            }
         }
    }
    
    void printTriggers(){
        if(!isEmpty(triggersCalculator)) println("\nCALCULATOR TRIGGERS");
        for(l <- triggersCalculator){
            println("  trig: <l> ===\>");
            for(calc <- triggersCalculator[l]) print(calc, "\t", facts);
        }
       if(!isEmpty(triggersRequirement)) println("\nREQUIREMENT TRIGGERS");
        for(l <- triggersRequirement){
            println("  trig: <l> ===\>");
            for(req <- triggersRequirement[l]) print(req, "\t", facts);
        }
    }
    
    void printDef2uses(){
        if(!isEmpty(def2uses)) println("\nDEFINE TO USES");
        for(def <- def2uses){
            println("\t<def> ==\> <def2uses[def]>");
        }
    }
    
     // Error reporting
    
    AType getTypeFromTree(Tree t) = getType(t);
    
    bool _report(FailMessage fm){
        if(getName(fm) == "_error"){
           throw checkFailed([fm]);
        } else {
            failMessages += fm;
            return true;
        }
    }
    
    bool _reports(list[FailMessage] fms){
        if (fms == []) {
            return true;
        }
        if(any(fm <- fms, getName(fm) == "_error")){
            throw checkFailed(fms);
        } else {
            failMessages += fms;
            return true;
        }
    }
    
    // ---- validation
    
    void validateTriggers(){
        return;
        int nissues = 0;
        for(calc <- calculators){
            deps = calcType(loc src, AType atype) := calc ? getDependencies(atype) : calc.dependsOn;
            
            for(dep <- deps){
                if(!(facts[dep]? || calc in (triggersCalculator[dep] ? {}))){
                    println("Not a fact or trigger for: <dep>");
                    print(calc, "\t", facts);
                    println("\t<calc>");
                    nissues += 1;
                }
            }
        }
    
        for(req <- requirements){
            for(dep <- req.dependsOn){
                if(!(facts[dep]? || req in (triggersRequirement[dep] ? {}))){
                    println("Not a fact or trigger for: <dep>");
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
        calcMap = ();
        dependencies = {};
        for(Calculator calc <- calculators){
            csrcs = calc has src ? [calc.src] : calc.srcs;
            for(src <-  csrcs){
                if(src in calcMap){
                    println("Multiple calculators for the same location");
                    print(calcMap[src], "\t", facts, full=false);
                    print(calc, "\t", facts, full=false);
                }
                calcMap[src] = calc;
            }
            dependencies += toSet(dependsOn(calc) - csrcs);
        }
        uses = {u.occ | u <- tm.uses};
        defs = tm.defines.defined;
        dependencies += {*req.dependsOn | req <- requirements};
        missing = dependencies - domain(calcMap) - domain(facts) - uses - defs;
        if(!isEmpty(missing)){
            printSolverState();
            throw TypePalUsage("Missing calculators for <missing>");
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
        
        for(calc <- triggersCalculator[trigger] ? {}){  
            evalOrScheduleCalc(calc);
        }
        
        for(req <- triggersRequirement[trigger] ? {}){
            evalOrScheduleReq(req);
        }
        
        for(Use u <- def2uses[trigger] ? {}){
            foundDefs = definedBy[u.occ];
            if({def} := foundDefs, facts[def]?){ 
                openUses -= u;
                addFact(u.occ, facts[def]);
                //if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ]>");
            } else {
                if(all(def <- foundDefs, facts[def]?)){ 
                   openUses -= u;
                   addFact(u.occ, overloadedAType({<def, definitions[def].idRole, instantiate(facts[def])> | def <- foundDefs}));
                   //if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ]>");
                }
            }
            
        }
    }
    
    // ---- Job management ----------------------------------------------------
    
    void solved(Calculator calc){
        solvedCalculatorJobs += calc;
        if(cdebug){ print("!"); print(calc, "", facts, full=false); }
    }
    
    void solved(Requirement req){
        solvedRequirementJobs += req;
        if(cdebug){ print("!"); print(req, "", facts, full=false); }
    }
  
    void updateJobs(){        
        calculators -= solvedCalculatorJobs;
        calculatorJobs -= solvedCalculatorJobs;
        solvedCalculatorJobs = {};
         
        requirements -= solvedRequirementJobs;
        requirementJobs -= solvedRequirementJobs;
        solvedRequirementJobs = {};
    }
    
    tuple[set[Calculator] calculators, set[Calculator] calculatorJobs, set[Calculator] solvedCalculatorJobs,
          set[Requirement] requirements, set[Requirement] requirementJobs, set[Requirement] solvedRequirementJobs,
          set[Use] openUses, map[loc,AType] facts, map[loc, AType] bindings, set[loc] activeTriggers] checkPointSolverState() {
        return <calculators, calculatorJobs, solvedCalculatorJobs, 
                requirements, requirementJobs, solvedRequirementJobs, openUses, facts, bindings, activeTriggers>;
    }
    
    void restoreSolverState(tuple[set[Calculator] calculators, set[Calculator] calculatorJobs, set[Calculator] solvedCalculatorJobs,
          set[Requirement] requirements, set[Requirement] requirementJobs, set[Requirement] solvedRequirementJobs,
           set[Use] openUses, map[loc,AType] facts, map[loc, AType] bindings, set[loc] activeTriggers]  cp){
          
          calculators = cp.calculators;
          calculatorJobs = cp.calculatorJobs;
          solvedCalculatorJobs = cp.solvedCalculatorJobs;
          requirements = cp.requirements;
          requirementJobs = cp.requirementJobs;
          solvedRequirementJobs = cp.solvedRequirementJobs;
          openUses = cp.openUses;
          if(cdebug){
              for(f <- domain(facts) - domain(cp.facts)){
                println("removing fact: <f> ==\> <facts[f]>");
              }
              for(f <- domain(facts)){
                if(cp.facts[f]? && cp.facts[f] != facts[f]){
                    println("restoring <f> from <facts[f]> to <cp.facts[f]>");
                }
              }
          }
          //facts = cp.facts;  
          bindings = cp.bindings;
          activeTriggers = cp.activeTriggers;
    } 
    
    // ---- Add a fact --------------------------------------------------------
    
    bool addFact(loc l, AType atype){
        iatype = instantiate(atype);
        facts[l] = iatype;
        if(cdebug)println("!fact <l> ==\> <iatype>");
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
    
    set[loc] getDependencies(AType atype){
        deps = {};
        visit(atype){
            case tv: tvar(loc src) : deps += src;
        };
        return deps; 
    }    
    
    // ---- Evaluate/schedule calculators -------------------------------------
    
    void evalOrScheduleCalc(Calculator calc){
        if(evalCalc(calc)){
            solved(calc);
        } else {
            scheduleCalc(calc);
        }
    }
    
    void scheduleCalc(Calculator calc, list[loc] dependsOn){
        if(calc notin calculatorJobs && calc notin solvedCalculatorJobs){
            nAvailable = 0;
            for(dep <- dependsOn) { if(facts[dep]?) nAvailable += 1; }
            enabled = nAvailable == size(dependsOn);
            if(enabled) calculatorJobs += calc;
            if(cdebug){ print(enabled ? "*" : "+"); print(calc, "", facts, full=false); }
        }
    }
    
    void scheduleCalc(calc:calcType(loc src, AType atype)){
        dependsOn = getDependencies(atype) - src; // <===
        scheduleCalc(calc, toList(dependsOn));
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
   
    bool evalCalc(calcType(loc src, AType atype)){
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
        
        return false;
    }
    
    bool evalCalc(calcLoc(loc src, [loc from])){
        try {
            facts[src] = getType(from);
            if(cdebug)println("!fact <src> ==\> <facts[src]>");
            fireTrigger(src);
            return true;
        } catch TypeUnavailable(): return false; /* cannot yet compute type */

        return false;
    }
    
    bool evalCalc(calc:calc(str cname, loc src, list[loc] dependsOn,  AType(Solver tm) getAType)){
        if(allDependenciesKnown(dependsOn, calc.eager)){
            try {
                facts[src] = instantiate(getAType(thisSolver));
                bindings2facts(bindings, src);
                if(cdebug)println("!fact <src> ==\> <facts[src]>");
                fireTrigger(src);
                return true;
            } catch TypeUnavailable(): return false; /* cannot yet compute type */
        }
        return false;
    }
    
    bool evalCalc(calcLub(str cname, list[loc] defines, list[loc] dependsOn, list[AType(Solver tm)] getATypes)){
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
                for(def <- defines) { facts[def] = tp; }
                for(def <- defines) { fireTrigger(def); }
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
        if(allDependenciesKnown(req.dependsOn, req.eager) && evalReq(req)){
            solved(req);  
        } else {
            scheduleReq(req);
        }
     }
    
    void scheduleReq(Requirement req){
        if(req notin requirementJobs && req notin solvedRequirementJobs){
           nAvailable = 0;
           for(dep <- req.dependsOn) { if(facts[dep]?) nAvailable += 1; }
           
           enabled = nAvailable == size(req.dependsOn);
           if(enabled) requirementJobs += req;
           if(cdebug){ print(enabled ? "*" : "+"); print(req, "", facts, full=false); }
       }
    }  
    
    bool evalReq(reqEqual(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!_equal(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false; 
        return false;
    }
    
    bool evalReq(reqComparable(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!_comparable(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
        return false;
    }
    
    bool evalReq(reqSubtype(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!_subtype(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
        return false;
    }
    
    bool evalReq(reqUnify(str rname, value l, value r, list[loc] dependsOn, FailMessage fm)){
        try {
            if(!_unify(getType(l), getType(r))) { failMessages += fm; }
            return true;
        } catch TypeUnavailable(): return false;
        return false;
    }
    
    bool evalReq(reqError(loc src, list[loc] dependsOn, FailMessage fm)){
        failMessages += fm;
        return true;
    }
    
    bool evalReq(reqErrors(loc src, list[loc] dependsOn, list[FailMessage] fms)){
        failMessages += fms;
        return true;
    }
    
    bool evalReq(req:req(str rname, loc src,  list[loc] dependsOn, void(Solver s) preds)){
        try {
            preds(thisSolver);
            bindings2facts(bindings, getReqSrc(req));
            solved(req);
        } catch TypeUnavailable(): return false;
        return false;
    }
    
    // Handle bindings resulting from unification
    
    // The binding of a type variable that occurs inside the scope of that type variable can be turned into a fact
    void bindings2facts(map[loc, AType] bindings, loc occ){
        if(!isEmpty(bindings)){
            for(b <- bindings){
               //if(cdebug) println("bindings2facts: <b>, <facts[b]? ? facts[b] : "**undefined**">");
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
                //case defType(AType atype): return atype;
                //case defType(Tree tree): instantiate(findType(tree@\loc));
                case defTypeCall(list[loc] dependsOn, AType(Solver s) getAType):
                    return getAType(thisSolver);
                case defTypeLub(list[loc] dependsOn, list[loc] defines, list[AType(Solver s)] getATypes):
                    throw "Cannot yet handle defTypeLub in getType";
                default: 
                    throw "getType cannot handle <v>";
            }
        
        } catch NoSuchKey(k):
            throw TypeUnavailable();
            
        throw "getType cannot handle <v>";
    }
    
    AType getTypeInScope0(str id, loc scope, set[IdRole] idRoles){
        foundDefs = lookupFun(tm, use(id, anonymousOccurrence, scope, idRoles));
        if({def} := foundDefs){
           return instantiate(facts[def]);
        } else {
          if(mayOverloadFun(foundDefs, definitions)){
            return overloadedAType({<d, idRole, instantiate(facts[d])> | d <- foundDefs, idRole := definitions[d].idRole, idRole in idRoles});
          } else {
             _reports([error(d, "Double declaration of %q in %v", id, foundDefs) | d <- foundDefs] /*+ error("Undefined `<id>` due to double declaration", u.occ) */);
          }
        }
    }
    
    //@memo
    AType _getTypeInScope(str id, loc scope, set[IdRole] idRoles){
        try {
            return getTypeInScope0(id, scope, idRoles);
        } catch NoSuchKey(k):
                throw TypeUnavailable();
        //catch NoBinding():
        //        throw TypeUnavailable();
    }
    
    rel[str, AType] getNamesInType(AType container,  set[IdRole] idRolesSel, loc scope){
    
    }
    
    AType _getTypeInType(AType containerType, Tree selector, set[IdRole] idRolesSel, loc scope){
        selectorLoc = getLoc(selector);
        selectorName = unescapeName("<selector>");
        <isNamedType, containerName, contRoles> = getTypeNameAndRole(containerType);
        if(isNamedType){
            overloads = {};
            unavailable = false;
            for(containerDef <- getDefinitions(containerName, scope, contRoles)){    
                try {
                    selectorType = getTypeInScope0(selectorName, containerDef.defined, idRolesSel);
                    overloads += <containerDef.defined, containerDef.idRole, instantiateTypeParameters(selector, getType(containerDef.defInfo), containerType, selectorType, thisSolver)>;
                 } catch TypeUnavailable():
                        unavailable = true;
                   catch NoSuchKey(k):
                        unavailable = true;
                   catch NoBinding(): {
                        try {
                            selectorType = getTypeInTypeFromDefineFun(containerDef, selectorName, idRolesSel, thisSolver);
                            overloads += <containerDef.defined, containerDef.idRole, instantiateTypeParameters(selector, getType(containerDef.defInfo), containerType, selectorType, thisSolver)>;
                        } catch TypeUnavailable():
                            unavailable = true;
                          catch NoBinding():
                            unavailable = true;
                           // _report(error(selector, "No definition for %v %q in type %t", intercalateOr([replaceAll(getName(idRole), "Id", "") | idRole <- idRolesSel]), "<selector>", containerType));
                    }
             }
             if(isEmpty(overloads)){
                if(unavailable) throw TypeUnavailable();
                _report(error(selector, "No definition for %v %q in type %t", intercalateOr([replaceAll(getName(idRole), "Id", "") | idRole <- idRolesSel]), "<selector>", containerType));
              } else if({<loc key, IdRole role, AType tp>} := overloads){
                addFact(selectorLoc, tp);
                return tp;
             } else {
                tp2 = overloadedAType(overloads);
                addFact(selectorLoc, tp2);
                return tp2;
             }
         } else {
            if(overloadedAType(rel[loc, IdRole, AType] overloads) := containerType){
                overloads = {};
                for(<key, role, tp> <- overloads){
                    try {
                        selectorType = getTypeInNamelessTypeFun(tp, selector, scope, thisSolver);
                        overloads += <key, role, selectorType>;
                    } catch checkFailed(list[Message] msgs): {
                        ; // do nothing and try next overload
                    } catch e:;  
                }
                if(isEmpty(overloads)){
                    _report(error(selector, "Cannot access fields on type %t", containerType));
                } else if({<key, role, tp>} := overloads){
                    addFact(selectorLoc, tp);
                    return tp;
                } else {
                    tp2 = overloadedAType(overloads);
                    addFact(selectorLoc, tp2);
                    return tp2;
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
         }
    }
     
    rel[str id, AType atype] _getAllDefinedInType(AType containerType, loc scope, set[IdRole] idRoles){
        <isNamedType, containerName, contRoles> = getTypeNameAndRole(containerType);
        if(isNamedType){
            results = {};
            try {
                for(containerDef <- getDefinitions(containerName, scope, contRoles)){   
                    try {
                        results += { <id, getType(def.defInfo)> |  tuple[str id, IdRole idRole, loc defined, DefInfo defInfo] def  <- defines[containerDef.defined] ? {}, def.idRole in idRoles };
                    } catch TypeUnavailable():; /* ignore */
                }
                return results;
             } catch AmbiguousDefinition(set[loc] foundDefs): {
                //if(!mayOverloadFun(foundDefs, definitions)){
                    messages += [error("Double declaration", defined) | defined  <- foundDefs];
                    return results;
                //}
                return results;
             }      
         } else {
            throw TypePalUsage("`getAllDefinedInType` is only defined on a named type, found `<prettyPrintAType(containerType)>`");
         }
    }
    
    Define getDefinition(Tree tree){
        try {
            println("getDefinition: <tree>,  <getLoc(tree)>");
            return definitions[getLoc(tree)];
         } catch NoSuchKey(k):
                throw TypeUnavailable();
           catch NoBinding(): {
                throw TypeUnavailable();
           }
    }
    
    set[Define] getDefinitions(str id, loc scope, set[IdRole] idRoles){
        try {
            foundDefs = lookupFun(tm, use(id, anonymousOccurrence, scope, idRoles));
            if({def} := foundDefs){
               return {definitions[def]};
            } else {
              if(mayOverloadFun(foundDefs, definitions)){
                return {definitions[def] | def <- foundDefs}; 
              } else {
                throw AmbiguousDefinition(foundDefs);
              }
            }
         } catch NoSuchKey(k):
                throw TypeUnavailable();
           catch NoBinding(): {
                println("getDefinitions: <id> in scope <scope> <idRoles> ==\> TypeUnavailable2");
                throw TypeUnavailable();
           }
    }
    
    set[Define] getDefinitions(Tree tree, set[IdRole] idRoles)
        = getDefinitions(getLoc(tree), idRoles);
    
    set[Define] getDefinitions(loc scope, set[IdRole] idRoles)
        = {<scope, id, idRole, defined, defInfo> | <str id, IdRole idRole, loc defined, DefInfo defInfo> <- tm.defines[scope], idRole in idRoles };
    
    // ---- "equal" and "requireEqual" ----------------------------------------
       
    bool _equal(AType given, AType expected){
        if(given == expected) return true;
        if(isFullyInstantiated(given) && isFullyInstantiated(expected)){
           return instantiate(unsetRec(given)) == instantiate(unsetRec(expected));
        }
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
        if(tvar(tname) := given){
            bindings[tname] = expected;
                return true;
        }
        if(tvar(tname) := expected){
            bindings[tname] = given;
                return true;
        }
        given2 = instantiate(given);
        expected2 = instantiate(expected);
        <ok, bindings1> = unify(given2, expected2, bindings);
        if(cdebug)println("unify(<given>, <expected>) ==\> <ok>, <bindings1>");
        if(ok){
            bindings += bindings1;
            return true;
        } else {
            return false;
        }
    }
    
    // ---- instantiate -------------------------------------------------------
    
     AType _instantiate(AType atype) = instantiate(atype);
    
    // ---- "subtype" and "requireSubtype" ------------------------------------
     
    bool _subtype(Tree given, AType expected) = _subtype(getType(given), expected);
    
    bool _subtype(AType given, Tree expected) = _subtype(given, getType(expected));
    
    bool _subtype(Tree given, Tree expected) = _subtype(getType(given), getType(expected));
    
    default bool _subtype(value given, value expected) { throw TypePalUsage("`subtype` called with <given> and <expected>"); }
    
    bool _subtype(AType small, AType large){
        if(isFullyInstantiated(small) && isFullyInstantiated(large)){
           return isSubTypeFun(small, large);
        } else {
          throw TypeUnavailable();
        }
    }
    
    void _requireSubtype(value given, value expected, FailMessage fm){
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
        for(t <- atypes){
            if(isFullyInstantiated(t)){
                lubbedType = getLubFun(lubbedType, t);
            } else {
                other += t; 
            }
        }
    
        if(lubbedType != theMinAType){
            bindings1 = bindings;
            bindings = ();
            other = [t | t <- other, !unify(lubbedType, t)];
            for(b <- bindings){
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

    bool allDependenciesKnown(set[loc] deps, bool eager)
        = isEmpty(deps) || (eager ? all(dep <- deps, facts[dep]?)
                                  : all(dep <- deps, facts[dep]?, isFullyInstantiated(facts[dep])));
    
    bool allDependenciesKnown(list[loc] deps, bool eager)
        = isEmpty(deps) || (eager ? all(dep <- deps, facts[dep]?)
                                  : all(dep <- deps, facts[dep]?, isFullyInstantiated(facts[dep])));
   
    bool allCalcDependenciesKnown(calcType(loc src, AType atype)){
        return true;
    }
    
    bool allCalcDependenciesKnown(calcLoc(loc src, list[loc] dependsOn)){
         return allDependenciesKnown(dependsOn - src, true);
    }
    
    default bool allCalcDependenciesKnown(Calculator calc){
        return allDependenciesKnown(calc.dependsOn, calc.eager);
    }
    
    bool isFullyInstantiated(AType atype){
        visit(atype){
            case tvar(loc tname): if(!facts[tname]? || tvar(tname) := facts[tname]) return false; // return facts[tname]? && isFullyInstantiated(facts[tname]);
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
            case tv: tvar(loc src) => substitute(tv)
            case lazyLub(list[AType] atypes) : {
                sbs = [substitute(tp) | tp <- atypes];
                insert simplifyLub(sbs);
                }
          };
    }
    
    // Unification of two types, for now, without checks on variables
    tuple[bool, map[loc, AType]] unify(AType t1, AType t2, map[loc, AType] bindings){
        //println("unify: <t1>, <t2>");
        if(t1 == t2) return <true, bindings>;
       
        if(tvar(loc tv1) := t1){
           if(bindings[tv1]?){
              return unify(bindings[tv1], t2, bindings);
           } else {
                return <true, (tv1 : t2) + bindings>;
           }
        }
          
        if(tvar(loc tv2) := t2){
           if(bindings[tv2]?){
              return unify(bindings[tv2], t1, bindings); 
           } else {
            return <true, (tv2 : t1) + bindings>;
          }
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
        if(lazyLub(lubbables1) := t1 && lazyLub(lubbables2) !:= t2){
            for(lb <- toSet(lubbables1)){
                if(tvar(loc tv) := lb){
                   bindings += (tv : t2) + bindings;
                }
            }
            return <true, bindings>;
        }
        
        if(lazyLub(lubbables1) !:= t1 && lazyLub(lubbables2) := t2){
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
        
    /*
     *  run: validates an extracted TModel via constraint solving
     *  
     */
    TModel _run(){
    
        int runStarted = cpuTime();
        
        configTypePal(tm.config);
        
        tm = tm.config.preSolver(tree, tm);
        
        // Initialize local state of Solver
   
        facts = tm.facts;
        defines = tm.defines;
        definesAdded = false;
        definitions = tm.definitions;
        bindings = ();
        messages = tm.messages;
        failMessages = [];
           
        println("<tm.modelName>, initial -- calculators: <size(calculators)>; requirements: <size(requirements)>; uses: <size(tm.uses)>; facts: <size(facts)>");
             
        if(cdebug){
            printTModel(tm);
        }
        
         validateDependencies();
        
        // Check for illegal overloading in the same scope
        if(cdebug) println("..... filter doubles in <size(defines)> defines");
        int now = cpuTime();
       
        for(<scope, id> <- defines<0,1>){
            foundDefines = defines[scope, id];
            if(size(foundDefines) > 1){
                 ds = {defined | <IdRole idRole, loc defined, DefInfo defInfo> <- foundDefines};
                if(!mayOverloadFun(ds, definitions)){
                    messages += [error("Double declaration of `<id>` in <foundDefines<1>>", defined) | <IdRole idRole, loc defined, DefInfo defInfo>  <- foundDefines];
                }
            }
        }
      
        int initFilterDoublesTime = cpuTime() - now;
       
        // Check that all uses have a definition and that all overloading is allowed
        if(cdebug) println("..... lookup <size(tm.uses)> uses");
        now = cpuTime();
         
        for(Use u <- tm.uses){
            try {
               foundDefs = lookupFun(tm, u);
               foundDefs = { fd | fd <- foundDefs, definitions[fd].idRole in u.idRoles };
               if(isEmpty(foundDefs)){
                    throw NoBinding();
               } else 
               if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                  definedBy[u.occ] = foundDefs;
                  for(def <- foundDefs) def2uses[def] = (def2uses[def] ? {}) + u;
                  openUses += u;
                  if(cdebug) println("!use  \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <foundDefs>");
                } else {
                    messages += [error("Double declaration", d) | d <- foundDefs] + error("Undefined `<getId(u)>` due to double declaration", u.occ);
                    if(cdebug) println("!use  \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** double declaration **");
                }
            }
            catch NoBinding(): {
                roles = size(u.idRoles) > 5 ? "" : intercalateOr([replaceAll(getName(idRole), "Id", "") | idRole <- u.idRoles]);
                messages += error("Undefined <roles> `<getId(u)>`", u.occ);
            }
        }
        int initCheckUsesTime = cpuTime() - now;
        
        // Process all defines (which may create new calculators/facts)
        
        now = cpuTime();
        if(cdebug) println("..... handle <size(defines)> defines");
        for(Define def <- defines){
            try {
                // TODO: enable when there is a config function to filter this
                //if(def.defined notin def2uses){ 
                //    if(def.id notin {"type"})
                //        messages += warning("Unused <def.id>", def.defined); 
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
        
        validateTriggers();
        
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
        updateJobs(); 
        int initFactTriggerTime = cpuTime() - now;
        
        // Try to evaluate or schedule the calculators
        now = cpuTime();
        if(cdebug) println("..... handle <size(calculators)> calculators");
 
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
        if(cdebug) println("..... handle <size(requirements)> requirement");
        for(Requirement req <- requirements){
            try {
                evalOrScheduleReq(req);
            } catch checkFailed(list[FailMessage] fms): {
                failMessages += fms;
             }
        }
        int initReqTime = cpuTime() - now;
        
        // Here we have jobs for calculators and requirements with known dependencies
        
      
        updateJobs();
      
        int mainStarted = cpuTime();
        int mainCalcTime = 0;
        int mainReqTime = 0;
        
        /****************** main solve loop *********************************/
        
        if(cdebug) println("..... start solving");
        
        int iterations = 0;
        int ncalculators = size(calculators);
        int nrequirements = size(requirements);
        int nfacts = size(facts);
        int nopenUses = size(openUses);
        
        solve(ncalculators, nrequirements, nfacts, nopenUses){ 
            iterations += 1;
            println("<tm.modelName>, iter #<iterations> -- calculators: <ncalculators>; calculatorJobs: <size(calculatorJobs)>; requirements: <nrequirements>; requirementJobs: <size(requirementJobs)>; uses: <size(openUses)>; facts: <size(facts)>; ");
       
            // ---- calculatorJobs
           
            now = cpuTime();
            for(Calculator calc <- calculatorJobs){
                 try {
                 	clearActiveTriggers();
                    if(evalCalc(calc)){
                       solved(calc);
                    } else {
                        if(cdebug){ print("?"); print(calc, "", facts, full=false); }
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
                    if(evalReq(req)){
                        solved(req);
                    } else {
                        if(cdebug){ print("?"); print(req, "", facts, full=false); }
                    }
                } catch checkFailed(list[FailMessage] fms): {
                    failMessages += fms;
                    solved(req);
                }
            }
            mainReqTime += cpuTime() - now;
            
            updateJobs();    
            ncalculators = size(calculators);
            nrequirements = size(requirements);
            nfacts = size(facts);
            nopenUses = size(openUses);
        }
           
        /****************** end of main solve loop *****************************/
           
        int mainEnded = cpuTime();
           
        if(cdebug) println("..... solving complete");
           
        tm.config.postSolver(tree, thisSolver);
        
        int postSolverTime = cpuTime() - mainEnded;
        
        // Convert all FaillMessages into Messages
        for(fm <- failMessages){
            messages += toMessage(fm, getType);
        }
        
        reportedLocations = { msg.at | msg <- messages };
        
        if(nopenUses + ncalculators + nrequirements > 0){
            println("<tm.modelName>, REMAINING <nopenUses> uses; <ncalculators> calculators; <nrequirements> requirements");
        }
        
        for (Use u <- openUses) {
            foundDefs = definedBy[u.occ];
            for(def <- foundDefs, !facts[u.occ]?, !alreadyReported(messages, u.occ)) {
                messages += error("Unresolved type for `<u has id ? u.id : u.ids>`", u.occ);
            }
        }
        
        calcNoLubs = [calc | calc <- calculators, !(calc is calcLub)];
      
        for(calc <- sort(calcNoLubs, bool(Calculator a, Calculator b){ return a.src.length < b.src.length; })){
            src = calc.src;
            if(!facts[src]?, !alreadyReported(messages, src)){
                cdeps = toSet(dependsOn(calc));
                if(!facts[src]? && isEmpty(reportedLocations & cdeps)){
                    messages += error("Unresolved type<calc has cname ? " for <calc.cname>" : "">", src);
                    reportedLocations += src;
                }
            }
        }
           
        calcLubs = [calc | calc <- calculators, calc is calcLub];
        for(calc <- calcLubs){
            csrcs = srcs(calc);
            cdeps = toSet(dependsOn(calc));
            for(src <- csrcs){
                if(!facts[src]? && isEmpty(reportedLocations & cdeps)){
                    messages += error("Unresolved type<calc has cname ? " for <calc.cname>" : "">", src);
                    reportedLocations += src;
                }
            }
        }
        
        //for(calc <- calculators, calc has src, !facts[calc.src]?, !alreadyReported(messages, calc.src)){
        //    messages += error("Unresolved type<calc has cname ? " for <calc.cname>" : "">" , calc.src);
        //}
        //
        //for(calc <- calculators){
        //    src = calc has src ? calc.src : (isEmpty(calc.srcs) ? |unknown:///| :calc.srcs[0]);
        //    if(!facts[src]? && !alreadyReported(messages, src)){
        //        deps = calc.dependsOn;
        //        forDeps = isEmpty(deps) ? "" : " for <for(int i <- index(deps)){><facts[deps[i]]? ? "`<prettyPrintAType(facts[deps[i]])>`" : "`unknown type of <deps[i]>`"><i < size(deps)-1 ? "," : ""> <}>";
        //        messages += error("Type <calc has cname ? " of <calc.cname>" : ""> could not be computed<forDeps>", src);
        //     }
        //}
           
        tm.calculators = calculators;
        tm.requirements = requirements;
      
        for(req <- requirements){
            src =  getReqSrc(req);
            if(isEmpty(reportedLocations & toSet(req.dependsOn)) && !alreadyReported(messages, src)){
                messages += error("Invalid <req.rname>; type of one or more subparts could not be inferred", src);
                reportedLocations += src;
            }
        }
        //for(req <- requirements, !alreadyReported(messages, getReqSrc(req))){
        //    messages += error("Invalid <req.rname>; type of one or more subparts could not be inferred", getReqSrc(req));
        //}
       
        if(cdebug){
            println("iterations: <iterations>; calculators: <ncalculators>; calculatorJobs: <size(calculatorJobs)>; requirements: <nrequirements>; requirementJobs: <size(requirementJobs)>; uses: <size(openUses)>; facts: <size(facts)>; ");
            printSolverState();
            //printTriggers();
            printDef2uses();
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
          tm.facts = facts;
          tm.messages = sortMostPrecise(toList(toSet(messages)));
         
          if(cdebug) println("Derived facts: <size(tm.facts)>");
          solverEnded = cpuTime();
          str fmt(int n) = right("<n>", 8);
          M = 1000000;
          println("<tm.modelName>, solver total: <(solverEnded - solverStarted)/M> ms; init: <(mainStarted - runStarted)/M> ms [ doubles <initFilterDoublesTime/M>; uses <initCheckUsesTime/M>; def <initDefTime/M>; register <initRegisterTime/M>; fact triggers <initFactTriggerTime/M>; calc <initCalcTime/M>; req <initReqTime/M> ]; run main loop: <(mainEnded - mainStarted)/M> ms [ calc <mainCalcTime/M>; req <mainReqTime/M> ]; finish: <(solverEnded - mainEnded)/M> ms [ postSolver <postSolverTime/M> ]");
          return tm;
    }
    
    // The actual code of newSolver
    
    Solver thisSolver = 
            solver(getType, 
                     _getTypeInScope,
                     _getTypeInType,
                     _getAllDefinedInType,
                     _equal,
                     _requireEqual,
                     _unify,
                     _requireUnify,
                     _comparable,
                     _requireComparable,
                     _requireTrue,
                     _requireFalse,
                     _instantiate,
                     isFullyInstantiated,
                     fact,
                     _subtype,
                     _requireSubtype,
                     _lub,
                     _lubList,
                     _run,
                     _report,
                     _reports,
                     _getConfig,
                     _getFacts,
                     _getStore,
                     getDefinitions
                     );
    return thisSolver;
}