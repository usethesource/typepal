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

extend analysis::typepal::AType;
extend analysis::typepal::Collector;
extend analysis::typepal::FailMessage;
extend analysis::typepal::Messenger;
extend analysis::typepal::ScopeGraph;
extend analysis::typepal::TypePalConfig;
extend analysis::typepal::Utils;

syntax ANONYMOUS_OCCURRENCE = "anonymous_occurence";
private loc anonymousOccurrence = ([ANONYMOUS_OCCURRENCE] "anonymous_occurence")@\loc;

// The Solver data type: a collection of call backs

data Solver
    = solver(
        AType(value) getType,
        AType (str id, loc scope, set[IdRole] idRoles) getTypeInScope,
        AType (Tree container, Tree selector, set[IdRole] idRolesSel, loc scope) getTypeInType,
        set[Define] (str id, loc scope, set[IdRole] idRoles) getDefinitions,
        void (value scope, str id, IdRole idRole, value def, DefInfo info) defineInScope,
        set[AType] (AType containerType, loc scope) getAllTypesInType,
        
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
        void (loc tvScope) keepBindings,
        void (value, AType) fact,
        
        bool (value, value) subtype,
        void (value, value, FailMessage) requireSubtype,
        
        AType (value, value) lub,
        AType (list[AType]) lubList,
        TModel () run,
        bool(FailMessage fm) report,
        bool (set[FailMessage]) reports,
        TypePalConfig () getConfig,
        TModel () getTModel
    );
    
Solver newSolver(TModel tm, bool debug = false){
    
    // Configuration (and related state)
    
    bool cdebug = debug;
    
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
        getTypeInNamelessTypeFun = tc.getTypeInNamelessType;
    }
    
    TypePalConfig getConfig() = tm.config;
    TModel getTModel() = tm;
    
    // State of Solver
    
    map[loc, AType] facts = ();
    set[Define] defines = {};
    bool definesAdded = false;
    
    set[Fact] openFacts = {};
    map[loc, Define] definitions = ();
    set[Requirement] openReqs = {};
    map[loc, AType] bindings = ();
    map[loc, set[Requirement]] triggersRequirement = ();
    map[loc, set[Fact]] triggersFact = ();
    
    set[Requirement] requirementJobs = {};
    
    list[Message] messages = [];
    
    void printState(){
        println("Derived facts:");
            for(loc fact <- facts){
                println("\t<fact>: <facts[fact]>");
            }
        if(size(openFacts) > 0){
            println("Unresolved facts:");
            for(Fact fact <- openFacts){
                if(fact has src){
                    println("\t<fact.src>"); 
                } else {
                    println("\t<fact.srcs>");
                }
                if(fact has uninstantiated){
                    println("\t  dependsOn: <fact.uninstantiated>");
                } else if(isEmpty(fact.dependsOn)){
                    println("\t  dependsOn: nothing");
                } else {
                    for(dep <- fact.dependsOn){
                        println("\t  dependsOn: <dep><facts[dep]? ? "" : " ** unavailable **">");
                    }
                }
                println("\t<fact>");
            }
        }
        if(size(openReqs) > 0){
            println("Unresolved requirements:");
            for(rq <- openReqs){
                println("\t<rq.rname> at <rq.src>:");
                for(atype <- rq.dependsOn){
                    println("\t  dependsOn: <atype><facts[atype]? ? "" : " ** unavailable **">");
                }
            }
        }
    }
    
    // Error reporting
    
    AType getTypeFromTree(Tree t) = getType(t);
    
    bool _report(FailMessage fm){
        msg = toMessage(fm, getTypeFromTree);
        if(getName(msg) == "error"){
           throw checkFailed({msg});
        } else {
            messages += msg;
            return true;
        }
    }
    
   bool _reports(set[FailMessage] fms){
        msgs = { toMessage(fm, getTypeFromTree) | fm <- fms };
        if(any(msg <- msgs, getName(msg) == "error")){
            throw checkFailed(msgs);
        } else {
            messages += msgs;
            return true;
        }
   }
    
    // Add a fact
   
    bool addFact(fct:openFact(loc src, AType uninstantiated)){
        if(!(uninstantiated is lazyLub)){
            try {
                iatype = getType(uninstantiated); //instantiate(uninstantiated); //getType(uninstantiated);
                if(!mayReplace(src, iatype)){ println("####1 <src>: <facts[src]> not replaced by <iatype>"); return true; }
                facts[src] = iatype;
                dependsOn = getDependencies(iatype);
                if(allDependenciesKnown(dependsOn, false) && src notin dependsOn) fireTriggers(src);
                return true;
            } catch TypeUnavailable(): /* cannot yet compute type */;
        }
        openFacts += fct;
        dependsOn = getDependencies(uninstantiated) - src; // <===
        for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
        fireTriggers(src);
        return false;
    }
    
    bool addFact(fct:openFact(loc src, set[loc] dependsOn,  AType(Solver tm) getAType)){
        //if(cdebug)println("addFact2: <fct>");
        if(allDependenciesKnown(dependsOn, true)){
            try {
                iatype = instantiate(getAType(thisSolver));
                if(!mayReplace(src, iatype)){ println("####2 <src>: <facts[src]> =!=\> <iatype>"); return true; }
                facts[src] = iatype;
                if(cdebug)println(" fact <src> ==\> <facts[src]>");
                fireTriggers(src);
                return true;
            } catch TypeUnavailable(): /* cannot yet compute type */;
        }
        openFacts += fct;
        for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
        fireTriggers(src);
        return false;
    }
    
    bool addFact(fct:openFact(set[loc] defines, set[loc] dependsOn, list[AType(Solver tm)] getATypes)){
        if(cdebug)println("addFact LUB: <fct>");
        
        if(allDependenciesKnown(dependsOn, true)){
            try {    
                computedTypes = [instantiate(getAType(thisSolver)) | getAType <- getATypes];
                if(any(tp <- computedTypes, tvar(l) := tp)) throw TypeUnavailable();
                tp = simplifyLub(computedTypes);
                //tp =  (getATypes[0]() | getLubFun(it, getAType()) | getAType <- getATypes[1..]);    
                for(def <- defines){ 
                   if(!mayReplace(def, tp)){
                      println("####3 <def>: <facts[def]> not replaced by <tp>");
                  } else {
                     facts[def] = tp;  
                     if(cdebug)println(" fact3 <def> ==\> <tp>");
                  }
                }
                for(def <- defines) { fireTriggers(def); }
                if(cdebug)println("\taddFact3: lub computed: <tp> for <defines>");
                return true;
            } catch TypeUnavailable(): /* cannot yet compute type */;
        }
        
        // try to partially compute the lub;
        //if(cdebug) println("try to partially compute the lub");
        knownTypes = ();
        solve(knownTypes){
            AType currentLub;
            for(int i <- index(getATypes)){
                try {
                    tp = getATypes[i](thisSolver);
                    if(isFullyInstantiated(tp)){
                        currentLub = currentLub? ? getLubFun(currentLub, tp) : tp;
                        knownTypes[i] = tp;
                    }
                } catch TypeUnavailable(): /*println("unavailable: <i>")*/;
            }
            
            if(currentLub?){
                for(def <- defines){ 
                    if(!mayReplace(def, currentLub)){
                        println("####4 <def>: <facts[def]> not replaced by <currentLub>");
                    } else {
                        facts[def] = currentLub; 
                    }
                }
                for(def <- defines) { 
                    try fireTriggers(def, protected=false); 
                    catch TypeUnavailable():
                        ;//facts = delete(facts, def);
                }
            }
        }
        if(size(knownTypes) == size(getATypes))
            return true;
        
        if(cdebug) println("last resort");
        // last resort
        openFacts += fct;
        //if(cdebug)println("\taddFact: adding dependencies: <dependsOn>");
        for(d <- dependsOn) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
        //for(d <- defines) triggersFact[d] = (triggersFact[d] ? {}) + {fct};
        for(def <- defines) fireTriggers(def);
        return false;
    }
    
    default void addFact(Fact fct) {
        throw TypePalInternalError("Cannot handle <fct>");
    }
    
    bool addFact(loc l, AType atype){
        //println("addFact: <l>, <atype>");
        iatype = instantiate(atype);
        if(!mayReplace(l, iatype)){ println("####5 <l>: <facts[l]> replaced by <iatype>"); /*return false;*/ }
        facts[l] = iatype;
        if(cdebug)println(" fact <l> ==\> <iatype>");
        if(tvar(tvloc) := iatype){
            triggersFact[tvloc] = (triggersFact[tvloc] ? {}) + {openFact(l, iatype)};
        } else {
            fireTriggers(l);
        }
        return true;
    }
    
    void fireTriggers(loc l, bool protected=true){
        //if(cdebug) println("\tfireTriggers: <l>");
        
        for(fct <- triggersFact[l] ? {}){        
            if(fct has uninstantiated || allDependenciesKnown(fct.dependsOn, true)){
               try {
                  if(cdebug) println("\tfireTriggers: adding fact: <fct>");
                  openFacts -= fct;
                  if(fct has src){
                     if(!facts[fct.src]? || tvar(x) := facts[fct.src]) addFact(fct);
                  } else {
                     addFact(fct);
                  }
               } catch TypeUnavailable(): {
                      /* cannot yet compute type */;
                      if(!protected){
                         throw TypeUnavailable();
                      }
                  }
            }
        }
        
        for(req <- triggersRequirement[l] ? {}){
            if(allDependenciesKnown(req.dependsOn, true)){
               requirementJobs += req;
               //if(cdebug)println("\tfireTriggers: adding requirementJob: <req.rname>, <req.src>");
            }
        }
    }
    
    // Handle bindings resulting from unification
    
    void clearBindings() { 
        if(!isEmpty(bindings)) 
            println("clearBindings: <bindings>");
        bindings = (); 
    }
    
    void keepBindings(loc tvScope) { 
        if(!isEmpty(bindings)){
            res = (b : bindings[b] | b <- bindings, containedIn(b, tvScope));
            //println("keepBindings, <tvScope>: <bindings> ==\> <res>");
           bindings = res;
        }
    }
    
    // The binding of a type variable that occurs inside the scope of that type variable can be turned into a fact
    void bindings2facts(map[loc, AType] bindings, loc occ){
       
        for(b <- bindings){
            if(cdebug) println("bindings2facts: <b>, <facts[b]? ? facts[b] : "**undefined**">");
            if(!facts[b]? || tvar(x) := facts[b]){
               addFact(b, bindings[b]);
               if(cdebug) println("bindings2facts, added: <b> : <bindings[b]>");
            } else {
               oldTp = facts[b];
               if(lazyLub(list[AType] atypes) := oldTp){
                  addFact(b, bindings[b]);
                  if(cdebug){ println("bindings2facts, added: <b> : <bindings[b]>"); }
               } else
               if(cdebug) println("bindings2facts, not added: <b>");
            }
        }
    }
       
    // Check whether a requirement is satisfied
    tuple[bool ok, list[Message] messages, map[loc, AType] bindings] satisfies(Requirement req){
        bindings = ();
        try {
            req.preds(thisSolver);
            bindings2facts(bindings, req.src);
            return <true, [], bindings>;
        } catch checkFailed(set[Message] msgs):
            return <false, [*msgs], bindings>;
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
                case defType(AType atype): return atype;
                case defGetType(Tree tree): instantiate(findType(tree@\loc));
                case defType(set[loc] dependsOn, AType(Solver s) getAType):
                    return getAType(thisSolver);
                case defLub(set[loc] dependsOn, set[loc] defines, list[AType(Solver s)] getATypes):
                    throw "Cannot yet handle defLub in getType";
            }
        
        } catch NoSuchKey(k):
            throw TypeUnavailable();
    }
    
    @memo
    AType getTypeInScope(str id, loc scope, set[IdRole] idRoles){
        try {
            foundDefs = lookupFun(tm, use(id, anonymousOccurrence, scope, idRoles));
            if({def} := foundDefs){
               return instantiate(facts[def]);
            } else {
              if(mayOverloadFun(foundDefs, definitions)){
                return overloadedAType({<d, idRole, instantiate(facts[d])> | d <- foundDefs, idRole := definitions[d].idRole, idRole in idRoles});
              } else {  
                //// If only overloaded due to different time stamp, use most recent.
                // <ok, def> = findMostRecentDef(foundDefs);
                //if(ok){                
                //    return instantiate(facts[def]);
                // }
                 _reports({error(d, "Double declaration of %q in %v", id, foundDefs) | d <- foundDefs} /*+ error("Undefined `<id>` due to double declaration", u.occ) */);
              }
            }
         } catch NoSuchKey(k): {
                throw TypeUnavailable();
                }
           catch NoBinding(): {
                //println("getType: <id> in scope <scope> as <idRoles> ==\> TypeUnavailable1");
                throw TypeUnavailable();
           }
    }
    
    AType getTypeInType(Tree container, Tree selector, set[IdRole] idRolesSel, loc scope){
        containerType = getType(container);
        <isNamedType, containerName, contRoles> = getTypeNameAndRole(containerType);
        if(isNamedType){
            overloads = {};
            for(containerDef <- getDefinitions(containerName, scope, contRoles)){    
                try {
                    selectorType = getTypeInScope("<selector>", containerDef.defined, idRolesSel);
                    //overloads += <containerDef.defined, containerDef.idRole, selectorType>;
                    overloads += <containerDef.defined, containerDef.idRole, instantiateTypeParameters(selector, getType(containerDef.defInfo), containerType, selectorType, thisSolver)>;
                 } catch TypeUnavailable():; /* ignore */
             }
             if(isEmpty(overloads)){
                _report(error(selector, "Type of %q could not be computed for %t", selector, containerType));
             } else {
                return overloadedAType(overloads);
             }
         } else {
            if(overloadedAType(rel[loc, IdRole, AType] overloads) := containerType){
                overloads = {};
                for(<key, role, tp> <- overloads){
                    try {
                        selectorType = getTypeInNamelessTypeFun(tp, selector, scope, thisSolver);
                        overloads += <key, role, selectorType>;
                    } catch checkFailed(set[Message] msgs): {
                        ; // do nothing and try next overload
                    } catch e:;  
                }
                if(isEmpty(overloads)){
                    _report(error(selector, "Cannot access fields on type %t", containerType));
                } else {
                    return overloadedAType(overloads);
                }
            } else {
                return getTypeInNamelessTypeFun(containerType, selector, scope, thisSolver);
            }
         }
     }
     
     set[AType] getAllTypesInType(AType containerType, loc scope){
        <isNamedType, containerName, contRoles> = getTypeNameAndRole(containerType);
        if(isNamedType){
            results = {};
            for(containerDef <- getDefinitions(containerName, scope, contRoles)){   
                try {
                    results += { getType(def.defInfo) |  tuple[str id, IdRole idRole, loc defined, DefInfo defInfo] def  <- defines[containerDef.defined] ? {} };
                } catch TypeUnavailable():; /* ignore */
            }
            return results;
         } else {
            throw "allTypesInType on <containerType>";
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
                //// If only overloaded due to different time stamp, use most recent.
                //<ok, def> = findMostRecentDef(foundDefs);
                //if(ok){        
                //    return {tm.definitions[def]};
                //}
                throw AmbiguousDefinition(foundDefs);
              }
            }
         } catch NoSuchKey(k):
                throw TypeUnavailable();
           catch NoBinding(): {
                //println("getDefinitions: <id> in scope <scope> ==\> TypeUnavailable2");
                throw TypeUnavailable();
           }
    }
    
    set[Define] getDefinitions(Tree tree, set[IdRole] idRoles)
        = getDefinitions(getLoc(tree), idRoles);
    
    set[Define] getDefinitions(loc scope, set[IdRole] idRoles)
        = {<scope, id, idRole, defined, defInfo> | <str id, IdRole idRole, loc defined, DefInfo defInfo> <- tm.defines[scope], idRole in idRoles };
    
    void defineInScope(value scope, str id, IdRole idRole, value def, DefInfo info){
        loc definingScope;
        if(Tree tscope := scope) definingScope = getLoc(tscope);
        else if(loc lscope := scope) definingScope = lscope;
        else throw TypePalUsage("Argument `scope` of `defineInScope` should be `Tree` or `loc`, found <typeOf(scope)>");
        
        loc l;
        if(Tree tdef := def) l = getLoc(tdef);
        else if(loc ldef := def) l = ldef;
        else throw TypePalUsage("Argument `def` of `defineInScope` should be `Tree` or `loc`, found <typeOf(def)>");
        
        id = unescapeName(id);
        if(info is defLub){
            throw TypePalUsage("`defLub` cannot be used in combination with `defineInScope`");
        } else {
            definesAdded = true;
            d = <definingScope, id, idRole, l, info>;
            tm.defines += {d};
            defines += {d};
            tm.definitions[l] = d;
            definitions[l] = d;
             
            dm = ();
            if(tm.definesMap[definingScope]?) dm = tm.definesMap[definingScope];
            dm[id] =  (dm[id] ? {}) + {<idRole, l>};
            tm.definesMap[definingScope] = dm;
            try addDefineAsFact(d);
            catch checkFailed(set[Message] msgs):
                messages += [*msgs];
        }
    }
    
    // ---- "equal" and "requireEqual" ----------------------------------------
       
    bool _equal(AType given, AType expected){
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
    
    AType lubList(list[AType] atypes) = simplifyLub(atypes);
     
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
                println("add <b>, <bindings[b]>");
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
        //println("findType: <src>");
        if(bindings[src]?){
            v = bindings[src];
            if(tvar(loc src1) := v && src1 != src && (bindings[src1]? || facts[src1]?)) return findType(src1);
            //println("findType==\> <v>");
            return v;
        }
        if(facts[src]?){
            v = facts[src];
            if(tvar(loc src1) := v && src1 != src && (bindings[src1]? || facts[src1]?)) return findType(src1);
            //println("findType==\> <v>");
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
        c1 = getName(t1); c2 = getName(t2);
        a1 = arity(t1); a2 = arity(t2);
        if(c1 != c2 || a1 != a2) return <false, bindings>;
       
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

    AType(Solver) makeGetType(Tree t) =
        AType(Solver s) { return s.getType(t); };
        
    bool addDefineAsFact(<loc scope, str id, IdRole idRole, loc defined, noDefInfo()>) 
        = true;
     
    bool addDefineAsFact(<loc scope, str id, IdRole idRole, loc defined, defType(AType atype)>) 
        = isFullyInstantiated(atype) ? addFact(defined, atype) : addFact(openFact(defined, atype));
        
    bool addDefineAsFact(<loc scope, str id, IdRole idRole, loc defined, defGetType(Tree t)>) {  
        tloc = getLoc(t);   
        return addFact(openFact(defined, {tloc}, makeGetType(t)));
    }
        
    bool addDefineAsFact(<loc scope, str id, IdRole idRole, loc defined, defType(set[loc] dependsOn, AType(Solver tm) getAType)>) 
        = addFact(openFact(defined, dependsOn, getAType));
    
    bool addDefineAsFact(<loc scope, str id, IdRole idRole, loc defined, defLub(set[loc] dependsOn, set[loc] defines, list[AType(Solver tm)] getATypes)>) 
        = addFact(openFact(defines, dependsOn, getATypes));
    
    default bool addDefineAsFact(Define d) {  throw TypePalInternalError("Cannot handle <d>"); }
    
    bool addFact(loc l, AType atype){
        //println("addFact: <l>, <atype>");
        iatype = instantiate(atype);
        if(!mayReplace(l, iatype)){ println("####5 <l>: <facts[l]> replaced by <iatype>");/* return false;*/ }
        facts[l] = iatype;
        if(cdebug)println(" fact <l> ==\> <iatype>");
        if(tvar(tvloc) := iatype){
            triggersFact[tvloc] = (triggersFact[tvloc] ? {}) + {openFact(l, iatype)};
        } else {
            fireTriggers(l);
        }
        return true;
    } 
    
    set[loc] getDependencies(AType atype){
        deps = {};
        visit(atype){
            case tv: tvar(loc src) : deps += src;
        };
        return deps;
    }
    
    // If we already have type info for a location, may we replace that with newer info?
    bool mayReplace(loc src, AType newType){
        if(!facts[src]?) return true;
        oldType = instantiate(facts[src]);
        if(tvar(x) := oldType) return true;
        if(tvar(x) := newType) return true;
        try {
            return oldType == newType || isSubTypeFun(oldType, newType);
        } catch TypePalUsage(s): return false;
    }
    
    /*
     *  run: validates an extracted TModel via constraint solving
     *  
     */
    TModel run(){
    
        configTypePal(tm.config);
        
        // Initialize local state of Solver
   
        facts = tm.facts;
        defines = tm.defines;
        definesAdded = false;
        definitions = tm.definitions;
        openFacts = tm.openFacts;
        bindings = ();
        openReqs = tm.openReqs;
        messages = tm.messages;
        triggersRequirement = ();
        triggersFact = ();   
        requirementJobs = {};
        namedTypes = tm.namedTypes;
        
        map[loc, set[loc]] definedBy = ();
        map[loc, Calculator] calculators = tm.calculators;
        set[Use] openUses = {};
        set[Use] notYetDefinedUses = {};
        
        int iterations = 0;
       
        if(cdebug){
           println("calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
           printTModel(tm);
        }
        
        if(cdebug) println("..... filter double declarations");
     
        // Check for illegal overloading in the same scope
        for(<scope, id> <- defines<0,1>){
            foundDefines = defines[scope, id];
            if(size(foundDefines) > 1){
                //<ok, def> = findMostRecentDef(foundDefines<1>);
                //if(!ok){
                    ds = {defined | <IdRole idRole, loc defined, DefInfo defInfo> <- foundDefines};
                    if(!mayOverloadFun(ds, definitions)){
                        messages += [error("Double declaration of `<id>` in <foundDefines<1>>", defined) | <IdRole idRole, loc defined, DefInfo defInfo>  <- foundDefines];
                    }
                //}
            }
        }
       
        if(cdebug) println("..... lookup uses");
        
        // Check that all uses have a definition and that all overloading is allowed
        for(Use u <- tm.uses){
            try {
               foundDefs = lookupFun(tm, u);
               
               if(isEmpty(foundDefs)){
                    notYetDefinedUses += u;
               } else 
               if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                  definedBy[u.occ] = foundDefs;
                  openUses += u;
                  if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <foundDefs>");
                } else {
                    messages += [error("Double declaration", d) | d <- foundDefs] + error("Undefined `<getId(u)>` due to double declaration", u.occ);
                    if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** double declaration **");
                }
            }
            catch NoBinding(): {
                    notYetDefinedUses += u;
            }
        }
        
        if(cdebug) println("..... handle defines");
    
        for(Define d <- defines){
            try addDefineAsFact(d);
            catch checkFailed(set[Message] msgs):
                messages += [*msgs];
        }
     
        if(cdebug) println("..... handle open facts");
        for(Fact f <- openFacts){
            try {
                 if(addFact(f)){
                    openFacts -= f;
                }
            } catch checkFailed(set[Message] msgs): 
                messages += [*msgs];
        } 
        
        if(cdebug) println("..... handle open requirements");
        for(Requirement oreq <- openReqs){
           for(dep <- oreq.dependsOn){
               triggersRequirement[dep] = (triggersRequirement[dep] ? {}) + {oreq};
               //println("add trigger <dep> ==\> <oreq.rname>");
           }
        }
    
        for(Requirement oreq <- openReqs){
            if(allDependenciesKnown(oreq.dependsOn, oreq.eager)){
               requirementJobs += oreq;
            }
        }
      
        /****************** main solve loop *********************************/
        
        if(cdebug) println("..... start solving");
        int nfacts = size(facts);
        int nopenReqs = size(openReqs);
        int nopenFacts = size(openFacts);
        int nopenUses = size(openUses);
        int nrequirementJobs = size(requirementJobs);
        int ncalculators = size(calculators);
        int nNotYetDefinedUses = size(notYetDefinedUses);
        
        solve(nfacts, nopenReqs, nopenFacts, nopenUses, nrequirementJobs, ncalculators, nNotYetDefinedUses){ 
            
            iterations += 1;
            
            println("iteration: <iterations>; calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
            
           // ---- notYetDefinedUses
           if(definesAdded){
               definesAdded = false;
               for(Use u <- notYetDefinedUses){
                   try {
                       foundDefs = lookupFun(tm, u);
                       
                       if(size(foundDefs) == 1 || mayOverloadFun(foundDefs, definitions)){
                          definedBy[u.occ] = foundDefs;
                          openUses += u;
                          notYetDefinedUses -= u;
                          if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <foundDefs>");
                        } else {
                            notYetDefinedUses -= u;
                            messages += [error("Double declaration", d) | d <- foundDefs] + error("Undefined `<getId(u)>` due to double declaration", u.occ);
                            if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> ** double declaration **");
                        }
                    }
                    catch NoBinding():
                        ;// Do nothing u is already on notYetDefinedUses
                }
            }
           
           // ---- openUses
           
           openUsesToBeRemoved = {};
           
           handleOpenUses:
           //for(Use u <- sort(openUses, bool(Use a, Use b){ return a.occ.offset < b.occ.offset; })){
           for(Use u <- openUses){
               foundDefs = definedBy[u.occ];
               if (cdebug) println("Consider unresolved use: <u>, foundDefs=<foundDefs>");
               
               try {
                   if({def} := foundDefs){  // unique definition found for use u
                       if(facts[def]?){     // has type of its definition become available?
                          addFact(u.occ, facts[def]);
                          openUsesToBeRemoved += u;
                          if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ]>");
                       } else {
                          if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ] ? "** unavailable **">");
                       }
                    } else {                // Multiple definitions found
                        foundDefs1 = {d | d <- foundDefs, definitions[d].idRole in u.idRoles}; 
                     
                        for(dkey <- foundDefs1){
                            try  { addDefineAsFact(definitions[dkey]); }
                            catch TypeUnavailable():
                                continue handleOpenUses;
                        }
                        
                        if(all(d <- foundDefs1, facts[d]?)){ 
                           addFact(u.occ, overloadedAType({<d, definitions[d].idRole, instantiate(facts[d])> | d <- foundDefs1}));
                           openUsesToBeRemoved += u;
                           if(cdebug) println("  use of \"<u has id ? u.id : u.ids>\" at <u.occ> ==\> <facts[u.occ]>");
                        }
                    }
                } catch checkFailed(set[Message] msgs):
                    messages += [*msgs];
           }
           
           openUses -= openUsesToBeRemoved;
          
           // ---- calculators
          
           calculatorsToBeRemoved = {};
           //for(loc calcloc <- sort(domain(calculators), bool(loc a, loc b){ return a.offset < b.offset; })){
           for(loc calcloc <- calculators){
              calc = calculators[calcloc];
              if(cdebug) println("?calc [<calc.cname>] at <calc.src>"); 
              if(allDependenciesKnown(calc.dependsOn, calc.eager)){
                  try {
                    t = calc.calculator(thisSolver);
                    addFact(calcloc, t);
                    bindings2facts(bindings, calc.src);
                    if(cdebug) println("+calc [<calc.cname>] at <calc.src> ==\> <t>"); 
                  } catch TypeUnavailable(): {
                    continue;
                  } catch checkFailed(set[Message] msgs): {
                    messages += [*msgs];
                    if(cdebug) println("-calc [<calc.cname>] at <calc.src> ==\> <msgs>");
                  }
                  calculatorsToBeRemoved += calcloc;
              }
           }
           calculators = domainX(calculators, calculatorsToBeRemoved);
           
           // ---- open requirements
           
           openFactsToBeRemoved = {};
           openReqsToBeRemoved = {};
           requirementJobsToBeRemoved = {};
           //for(Requirement oreq <- sort(requirementJobs, bool(Requirement a, Requirement b){ return a.src.offset < b.src.offset; })){
           for(Requirement oreq <- requirementJobs){
              if(allDependenciesKnown(oreq.dependsOn, oreq.eager)){  
                 try {       
                     <ok, messages1, bindings1> = satisfies(oreq); 
                     messages += messages1;
                     if(ok){
                        for(tv <- domain(bindings1), f <- triggersFact[tv] ? {}){
                            if(f has uninstantiated){
                             try {
                                    if(addFact(f.src, instantiate(f.uninstantiated)))
                                       openFactsToBeRemoved += f;
                                } catch TypeUnavailable(): /* cannot yet compute type */;
                            }
                            else if(allDependenciesKnown(f.dependsOn, true)){
                                try {
                                    if(addFact(f.src, f.getAType(thisSolver)))
                                       openFactsToBeRemoved += f;
                                } catch TypeUnavailable(): /* cannot yet compute type */;
                            }
                        }
                     }
                     if(cdebug)println("<ok ? "+" : "-">requ [<oreq.rname>] at <oreq.src>");
                     openReqsToBeRemoved += oreq;
                     requirementJobsToBeRemoved += oreq;
                 } catch TypeUnavailable():/* cannot yet compute type */;
               }
             }
             
             openFacts -= openFactsToBeRemoved;
             openReqs -= openReqsToBeRemoved;
             requirementJobs -= requirementJobsToBeRemoved;
             
             // ---- open facts
             
             if(cdebug) println("..... handle openFacts");
        
             openFactsToBeRemoved = {};
             //for(Fact fct <- sort(openFacts, 
             //                     bool(Fact a, Fact b){
             //                       asrc = a has src ? a.src.offset : sort(a.srcs)[0].offset;
             //                       bsrc = b has src ? b.src.offset : sort(b.srcs)[0].offset;
             //                       return asrc < bsrc; })){
             for(Fact fct <- openFacts){
                 try {
                    if(addFact(fct))
                        openFactsToBeRemoved += fct;
                 } catch checkFailed(set[Message] msgs):
                        messages += [*msgs];
             }
             openFacts -= openFactsToBeRemoved;         
             
             if(iterations >= 0){  // stop updating counters => stop solve
                nfacts = size(facts);
                nopenReqs = size(openReqs);
                nopenFacts = size(openFacts);
                nopenUses = size(openUses);
                nrequirementJobs = size(requirementJobs);
                ncalculators = size(calculators);   
                nNotYetDefinedUses = size(notYetDefinedUses); 
             }        
           }
           
           /****************** end of main solve loop *****************************/
           
           if(cdebug) println("..... solving complete");
           
           //iprintln(facts, lineLimit=10000);
           
           for(Use u <- notYetDefinedUses){
                roles = size(u.idRoles) > 5 ? "" : intercalateOr([replaceAll(getName(idRole), "Id", "") | idRole <- u.idRoles]);
                messages += error("Undefined <roles> `<getId(u)>`", u.occ);
           }
        
           for (Use u <- openUses) {
              foundDefs = definedBy[u.occ];
              for(def <- foundDefs){
                  if (facts[def]?) {
                    messages += [ error("Unresolved type for `<u has id ? u.id : u.ids>`", u.occ)];
                  }
              }
           }
           
           for(fct <- openFacts){
               if(fct has src){
                  messages += [ error("Unresolved type", fct.src)];
               }
           }
        
           for(loc l <- sort(domain(calculators), bool(loc a, loc b) { return a.length < b.length; })){
               calc = calculators[l];
               if(!alreadyReported(messages, calc.src)){
                  deps = calc.dependsOn;
                  forDeps = isEmpty(deps) ? "" : " for <for(int i <- index(deps)){><facts[deps[i]]? ? "`<prettyPrintAType(facts[deps[i]])>`" : "`unknown type of <deps[i]>`"><i < size(deps)-1 ? "," : ""> <}>";
                  messages += error("Type of <calc.cname> could not be computed<forDeps>", calc.src);
               }
           }
           
           tm.calculators = calculators;
           tm.openReqs = openReqs;
      
           for(req <- openReqs, !alreadyReported(messages, req.src)){
               messages += error("Invalid <req.rname>; type of one or more subparts could not be inferred", req.src);
           }
       
           if(cdebug){
               //println("----");
               println("iterations: <iterations>; calculators: <size(calculators)>; facts: <size(facts)>; openFacts: <size(openFacts)>; openReqs: <size(openReqs)>");
               printState();
               if(size(calculators) > 0){
                   println("Unresolved calculators:");
                   for(c <- calculators){
                        calc = calculators[c];
                        println("\t<calc.cname> at <calc.src>:");
                        for(atype <- calc.dependsOn){
                            println("\t  dependsOn: <atype><facts[atype]? ? "" : " ** unavailable **">");
                        }
                   }
               }
               
               //println("----");
               if(isEmpty(messages) && isEmpty(openReqs) && isEmpty(openFacts)){
                  println("No type errors found");
               } else {
                  println("Errors:");
                  for(msg <- messages){
                      println(msg);
                  }
                  if(!isEmpty(openReqs)) println("*** <size(openReqs)> unresolved requirements ***");
                  if(!isEmpty(openFacts)) println("*** <size(openFacts)> open facts ***");
               }
           }
           tm.facts = facts;
           tm.messages = sortMostPrecise([*messages]);
         
           if(cdebug) println("Derived facts: <size(tm.facts)>");
           return tm;
    }
    
    // The actual code of newSolver
    
    Solver thisSolver = 
            solver(getType, 
                     getTypeInScope,
                     getTypeInType,
                     getDefinitions,
                     defineInScope,
                     getAllTypesInType,
                     _equal,
                     _requireEqual,
                     _unify,
                     _requireUnify,
                     _comparable,
                     _requireComparable,
                     _requireTrue,
                     _requireFalse,
                     instantiate,
                     isFullyInstantiated,
                     keepBindings,
                     fact,
                     _subtype,
                     _requireSubtype,
                     _lub,
                     lubList,
                     run,
                     _report,
                     _reports,
                     getConfig,
                     getTModel
                     );
    return thisSolver;
}