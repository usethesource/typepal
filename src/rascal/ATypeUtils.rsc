
@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Jurgen J. Vinju - Jurgen.Vinju@cwi.nl - CWI}
@contributor{Mark Hills - Mark.Hills@cwi.nl (CWI)}
@contributor{Anastasia Izmaylova - Anastasia.Izmaylova@cwi.nl (CWI)}
module rascal::ATypeUtils

import List;
import Set;
import String;
extend ParseTree;

extend rascal::AType;

import lang::rascal::types::AbstractName;
import lang::rascal::\syntax::Rascal;

@doc{Annotation for parameterized types indicating whether the bound was explicitly given.}
public anno bool Symbol@boundGiven;

//@doc{Extension to add new types used internally during name resolution and checking.}
//public data Symbol =
//      \user(RName rname, list[Symbol] parameters)
//    | failure(set[Message] messages)
//    | \inferred(int uniqueId)
//    | \overloaded(set[Symbol] overloads, set[Symbol] defaults)
//    | deferred(Symbol givenType)
//    ;

@doc{Extension to add a production type.}
public data Symbol = \prod(Symbol \sort, str name, list[Symbol] parameters, set[Attr] attributes);

@doc{Annotations to hold the type assigned to a tree.}
public anno Symbol Tree@rtype;

@doc{Annotations to hold the location at which a type is declared.}
public anno loc Symbol@at; 

Symbol normalizeType(Symbol s){
   return
    visit(s){
        case Symbol::alist(Symbol::atuple(list[Symbol] tls)) => Symbol::alrel(tls)
        case Symbol::aset(Symbol::atuple(list[Symbol] tls))  => Symbol::arel(tls)
   }
}

@doc{Pretty printer for Rascal abstract types.}
str prettyPrintAType(aint()) = "int";
str prettyPrintAType(abool()) = "bool";
str prettyPrintAType(areal()) = "real";
str prettyPrintAType(arat()) = "rat";
str prettyPrintAType(astr()) = "str";
str prettyPrintAType(anum()) = "num";
str prettyPrintAType(anode()) = "node";
str prettyPrintAType(avoid()) = "void";
str prettyPrintAType(avalue()) = "value";
str prettyPrintAType(aloc()) = "loc";
str prettyPrintAType(adatetime()) = "datetime";
str prettyPrintAType(alabel(str s, AType t)) = "<prettyPrintAType(t)> <s>";
str prettyPrintAType(aparameter(str pn, AType t)) = "&<pn> \<: <prettyPrintAType(t)>";
str prettyPrintAType(aset(AType t)) = "set[<prettyPrintAType(t)>]";
str prettyPrintAType(arel(AType ts)) = "rel[<prettyPrintAType(ts)>]";
str prettyPrintAType(alrel(AType ts)) = "lrel[<prettyPrintAType(ts)>]";
str prettyPrintAType(atuple(AType ts)) = "tuple[<prettyPrintAType(ts)>]";
str prettyPrintAType(alist(AType t)) = "list[<prettyPrintAType(t)>]";
str prettyPrintAType(amap(AType d, AType r)) = "map[<prettyPrintAType(d)>, <prettyPrintAType(r)>]";
str prettyPrintAType(abag(AType t)) = "bag[<prettyPrintAType(t)>]";
str prettyPrintAType(\adt(str s, atypeList([]))) = s;
str prettyPrintAType(\adt(str s, atypeList(ps))) = "<s>[<prettyPrintAType(ps)>]" when size(ps) > 0;
str prettyPrintAType(acons(RName rn, str consName, AType fs, list[Keyword] kwFormals)) = "<convertName(rn)> <name> : (<prettyPrintAType(fs)>)";
str prettyPrintAType(aalias(str s, atypeList([]), AType t)) = "alias <s> = <prettyPrintAType(t)>";
str prettyPrintAType(aalias(str s, atypeList(ps), AType t)) = "alias <s>[<prettyPrintAType(ps)>] = <prettyPrintAType(t)>" when size(ps) > 0;
//str prettyPrintAType(AType s:afunc(AType rt, list[AType] ps)) = "fun <prettyPrintAType(rt)>(<intercalate(", ", [ prettyPrintAType(p) | p <- ps])>";
str prettyPrintAType(afunc(AType rt, atypeList(ps), list[AType] kw)) = "fun <prettyPrintAType(rt)>(<prettyPrintAType(ps)><isEmpty(kw) ? "" : ", "><intercalate(", ", [ prettyPrintAType(p) | p <- kw])>)";
str prettyPrintAType(\var-func(AType rt, atypeList(ps), AType va)) = "fun <prettyPrintAType(rt)>(prettyPrintAType(ps+val))>...)";
str prettyPrintAType(areified(AType t)) = "type[<prettyPrintAType(t)>]";

str prettyPrintAType(acons(str adtName, str consName, 
                 lrel[AType fieldType, str fieldName] fields, 
                 lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields))
                 = "<adtName>:<consName>(<intercalate(",", ["<prettyPrintAType(ft)> <fn>" | <ft, fn> <- fields])>,<intercalate(",", ["<prettyPrintAType(ft)> <fn>=..." | <ft, fn, de> <- kwFields])>)";

str prettyPrintAType(afunc(AType ret, list[AType] formals, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals))
                = "<prettyPrintAType(ret)>(<intercalate(",", [prettyPrintAType(f) | f <- formals])>,<intercalate(",", ["<prettyPrintAType(ft)> <fn>=..." | <ft, fn, de> <- kwFormals])>)";
str prettyPrintAType(amodule(str mname)) = "module <mname>";               
str prettyPrintAType(overloadedAType(rel[Key, AType] overloads))
                = "overloaded(" + intercalate(", ", [prettyPrintAType(t) | <k, t> <- overloads]) + ")";

//str prettyPrintAType(\user(RName rn, list[Symbol] ps)) = "<prettyPrintName(rn)>[<intercalate(", ", [ prettyPrintAType(p) | p <- ps ])>]";
//str prettyPrintAType(failure(set[Message] ms)) = "fail"; // TODO: Add more detail?
//str prettyPrintAType(\inferred(int n)) = "inferred(<n>)";
//str prettyPrintAType(\overloaded(set[Symbol] os, set[Symbol] defaults)) = "overloaded:\n\t\t<intercalate("\n\t\t",[prettyPrintAType(\o) | \o <- os + defaults])>";
//str prettyPrintAType(deferred(Symbol givenType)) = "deferred(<prettyPrintAType(givenType)>)";
// named non-terminal symbols
//str prettyPrintAType(\sort(str name)) = name;
//str prettyPrintAType(\start(Symbol s)) = "start[<prettyPrintAType(s)>]";
//str prettyPrintAType(\prod(Symbol s, str name, list[Symbol] fs, set[Attr] atrs)) = "<prettyPrintAType(s)> <name> : (<intercalate(", ", [ prettyPrintAType(f) | f <- fs ])>)";
//str prettyPrintAType(\lex(str name)) = name;
//str prettyPrintAType(\layouts(str name)) = name;
//str prettyPrintAType(\keywords(str name)) = name;
//str prettyPrintAType(aparameterized-sort(str name, list[Symbol] parameters)) = name when size(parameters) == 0;
//str prettyPrintAType(aparameterized-sort(str name, list[Symbol] parameters)) = "<name>[<intercalate(", ", [ prettyPrintAType(p) | p <- parameters ])>]" when size(parameters) > 0;
//str prettyPrintAType(aparameterized-lex(str name, list[Symbol] parameters)) = name when size(parameters) == 0;
//str prettyPrintAType(aparameterized-lex(str name, list[Symbol] parameters)) = "<name>[<intercalate(", ", [ prettyPrintAType(p) | p <- parameters ])>]" when size(parameters) > 0;
//// terminal symbols
//str prettyPrintAType(\lit(str string)) = string;
//str prettyPrintAType(\cilit(str string)) = string;
//str prettyPrintAType(\char-class(list[CharRange] ranges)) = "[<intercalate(" ", [ "<r.begin>-<r.end>" | r <- ranges ])>]";
//// regular symbols
//str prettyPrintAType(\empty()) = "()";
//str prettyPrintAType(\opt(Symbol symbol)) = "<prettyPrintAType(symbol)>?";
//str prettyPrintAType(\iter(Symbol symbol)) = "<prettyPrintAType(symbol)>+";
//str prettyPrintAType(\iter-star(Symbol symbol)) = "<prettyPrintAType(symbol)>*";
//str prettyPrintAType(\iter-seps(Symbol symbol, list[Symbol] separators)) = "{<prettyPrintAType(symbol)> <intercalate(" ", [ prettyPrintAType(sep) | sep <- separators ])>}+";
//str prettyPrintAType(\iter-star-seps(Symbol symbol, list[Symbol] separators)) = "{<prettyPrintAType(symbol)> <intercalate(" ", [ prettyPrintAType(sep) | sep <- separators ])>}*";
//str prettyPrintAType(\alt(set[Symbol] alternatives)) = "( <intercalate(" | ", [ prettyPrintAType(a) | a <- alternatives ])> )" when size(alternatives) > 1;
//str prettyPrintAType(\seq(list[Symbol] sequence)) = "( <intercalate(" ", [ prettyPrintAType(a) | a <- sequence ])> )" when size(sequence) > 1;
//str prettyPrintAType(\conditional(Symbol symbol, set[Condition] conditions)) = "<prettyPrintAType(symbol)> { <intercalate(" ", [ prettyPrintCond(cond) | cond <- conditions ])> }";
//default str prettyPrintAType(Symbol s) = "<type(s,())>";

//private str prettyPrintCond(Condition::\follow(Symbol symbol)) = "\>\> <prettyPrintAType(symbol)>";
//private str prettyPrintCond(Condition::\not-follow(Symbol symbol)) = "!\>\> <prettyPrintAType(symbol)>";
//private str prettyPrintCond(Condition::\precede(Symbol symbol)) = "<prettyPrintAType(symbol)> \<\<";
//private str prettyPrintCond(Condition::\not-precede(Symbol symbol)) = "<prettyPrintAType(symbol)> !\<\<";
//private str prettyPrintCond(Condition::\delete(Symbol symbol)) = "???";
//private str prettyPrintCond(Condition::\at-column(int column)) = "@<column>";
//private str prettyPrintCond(Condition::\begin-of-line()) = "^";
//private str prettyPrintCond(Condition::\end-of-line()) = "$";
//private str prettyPrintCond(Condition::\except(str label)) = "!<label>";

@doc{Create a new int type.}
AType makeIntType() = aint();

@doc{Create a new bool type.}
AType makeBoolType() = abool();

@doc{Create a new real type.}
AType makeRealType() = areal();

@doc{Create a new rat type.}
AType makeRatType() = arat();

@doc{Create a new str type.}
AType makeStrType() = astr();

@doc{Create a new num type.}
AType makeNumType() = anum();

@doc{Create a new node type.}
AType makeNodeType() = anode();

@doc{Create a new void type.}
AType makeVoidType() = avoid();

@doc{Create a new value type.}
AType makeValueType() = avalue();

@doc{Create a new loc type.}
AType makeLocType() = aloc();

@doc{Create a new datetime type.}
AType makeDateTimeType() = adatetime();

@doc{Create a new set type, given the element type of the set.}
AType makeSetType(AType elementType) {
    return isTupleType(elementType) ? makeRelTypeFromTuple(elementType) : aset(elementType);
}

@doc{Create a new list type, given the element type of the list.}
AType makeListType(AType elementType) {
    return isTupleType(elementType) ? makeListRelTypeFromTuple(elementType) : alist(elementType);
}       

@doc{Create a new rel type, given the element types of the fields. Check any given labels for consistency.}
AType makeRelType(AType elementTypes...) {
    set[str] labels = { l | alabel(l,_) <- elementTypes };
    if (size(labels) == 0 || size(labels) == size(elementTypes)) 
        return arel(elementTypes);
    else
        throw "For rel types, either all fields much be given a distinct label or no fields should be labeled."; 
}

@doc{Create a new rel type based on a given tuple type.}
AType makeRelTypeFromTuple(AType t) = arel(getTupleFields(t));

@doc{Create a new list rel type, given the element types of the fields. Check any given labels for consistency.}
AType makeListRelType(AType elementTypes...) {
    set[str] labels = { l | alabel(l,_) <- elementTypes };
    if (size(labels) == 0 || size(labels) == size(elementTypes)) 
        return alrel(elementTypes);
    else
        throw "For lrel types, either all fields much be given a distinct label or no fields should be labeled."; 
}

@doc{Create a new lrel type based on a given tuple type.}
AType makeListRelTypeFromTuple(AType t) = alrel(getTupleFields(t));

@doc{Create a new tuple type, given the element types of the fields. Check any given labels for consistency.}
AType makeTupleType(AType elementTypes...) {
    set[str] labels = { l | alabel(l,_) <- elementTypes };
    if (size(labels) == 0 || size(labels) == size(elementTypes)) 
        return atuple(elementTypes);
    else
        throw "For tuple types, either all fields much be given a distinct label or no fields should be labeled."; 
}

@doc{Create a new map type, given the types of the domain and range. Check to make sure field names are used consistently.}
AType makeMapType(AType domain, Symbol range) {
    if (alabel(l1,t1) := domain && alabel(l2,t2) := range && l1 != l2)
        return amap(domain,range);
    else if (alabel(l1,t1) := domain && alabel(l2,t2) := range && l1 == l2)
        throw "The field names of the map domain and range must be distinct.";
    else if (alabel(l1,t1) := domain)
        return amap(t1,range);
    else if (alabel(l2,t2) := range)
        return amap(domain,t2);
    else
        return amap(domain,range);
}

@doc{Create a new map type based on the given tuple.}
AType makeMapTypeFromTuple(AType t) {
    list[Symbol] tf = getTupleFields(t);
    if (size(tf) != 2)
        throw "The provided tuple must have exactly 2 fields, one for the map domain and one for the range.";
    return makeMapType(tf[0],tf[1]);
}

@doc{Create a new bag type, given the element type of the bag.}
AType makeBagType(AType elementType) = abag(elementType);

@doc{Create a new ADT type with the given name.}
AType makeADTType(str n) = \adt(n,[]);

@doc{Create a new parameterized ADT type with the given type parameters}
AType makeParameterizedADTType(str n, Symbol p...) = \adt(n,p);

@doc{Create a new constructor type.}
AType makeConstructorType(AType adtType, str name, Symbol consArgs...) {    
    set[str] labels = { l | alabel(l,_) <- consArgs };
    if (size(labels) == 0 || size(labels) == size(consArgs)) 
        return acons(adtType, name, consArgs);
    else
        throw "For constructor types, either all arguments much be given a distinct label or no parameters should be labeled."; 
}

@doc{Create a new constructor type based on the contents of a tuple.}
AType makeConstructorTypeFromTuple(AType adtType, str name, Symbol consArgs) {    
    return makeConstructorType(adtType, name, getTupleFields(consArgs)); 
}

@doc{Create a new alias type with the given name and aliased type.}
AType makeAliasType(str n, Symbol t) = aalias(n,[],t);

@doc{Create a new parameterized alias type with the given name, aliased type, and parameters.}
AType makeParameterizedAliasType(str n, Symbol t, list[Symbol] params) = aalias(n,params,t);

@doc{Marks if a function is a var-args function.}
public anno bool Symbol@isVarArgs;

@doc{Create a new function type with the given return and parameter types.}
AType makeFunctionType(AType retType, bool isVarArgs, Symbol paramTypes...) {
    set[str] labels = { l | alabel(l,_) <- paramTypes };
    if (size(labels) == 0 || size(labels) == size(paramTypes))
        //if (isVarArgs) { 
        //  return \var-func(retType, head(paramTypes,size(paramTypes)-1), last(paramTypes));
        //} else {
            return afunc(retType, paramTypes, [])[@isVarArgs=isVarArgs];
        //}
    else
        throw "For function types, either all parameters much be given a distinct label or no parameters should be labeled."; 
}

@doc{Create a new function type with parameters based on the given tuple.}
AType makeFunctionTypeFromTuple(AType retType, bool isVarArgs, Symbol paramTypeTuple) { 
    return makeFunctionType(retType, isVarArgs, getTupleFields(paramTypeTuple));
}

@doc{Create a type representing the reified form of the given type.}
AType makeReifiedType(AType mainType) = areified(mainType);

@doc{Create a type representing a type parameter (type variable).}
AType makeTypeVar(str varName) = aparameter(varName, avalue())[@boundGiven=false];

@doc{Create a type representing a type parameter (type variable) and bound.}
AType makeTypeVarWithBound(str varName, Symbol varBound) = aparameter(varName, varBound)[@boundGiven=true];

@doc{Unwraps aliases, parameters, and labels from around a type.}
AType unwrapType(aalias(_,_,at)) = unwrapType(at);
AType unwrapType(aparameter(_,tvb)) = unwrapType(tvb);
AType unwrapType(alabel(_,ltype)) = unwrapType(ltype);
AType unwrapType(\conditional(sym,_)) = unwrapType(sym);
public default Symbol unwrapType(AType t) = t;

@doc{Get the type that has been reified and stored in the reified type.}
public Symbol getReifiedType(AType t) {
    if (areified(rt) := unwrapType(t)) return rt;
    throw "getReifiedType given unexpected type: <prettyPrintAType(t)>";
}

@doc{Get the type of the relation fields as a tuple.}
public Symbol getRelElementType(AType t) {
    if (arel(ets) := unwrapType(t)) return atuple(ets);
    if (aset(tup) := unwrapType(t)) return tup;
    throw "Error: Cannot get relation element type from type <prettyPrintAType(t)>";
}

@doc{Get whether the rel has field names or not.}
bool relHasFieldNames(AType t) {
    if (arel(tls) := \unwrapType(t)) return size(tls) == size([ti | ti:alabel(_,_) <- tls]);
    throw "relHasFieldNames given non-Relation type <prettyPrintAType(t)>";
}

@doc{Get the field names of the rel fields.}
public list[str] getRelFieldNames(AType t) {
    if (arel(tls) := unwrapType(t) && relHasFieldNames(t)) return [ l | alabel(l,_) <- tls ];
    if (arel(_) := unwrapType(t)) throw "getRelFieldNames given rel type without field names: <prettyPrintAType(t)>";        
    throw "getRelFieldNames given non-Relation type <prettyPrintAType(t)>";
}

@doc{Get the fields of a relation.}
public list[Symbol] getRelFields(AType t) {
    if (arel(tls) := unwrapType(t)) return tls;
    if (aset(atuple(tls)) := unwrapType(t)) return tls;
    throw "getRelFields given non-Relation type <prettyPrintAType(t)>";
}

@doc{Get the type of the list relation fields as a tuple.}
public Symbol getListRelElementType(AType t) {
    if (alrel(ets) := unwrapType(t)) return atuple(ets);
    if (alist(tup) := unwrapType(t)) return tup;
    throw "Error: Cannot get list relation element type from type <prettyPrintAType(t)>";
}

@doc{Get whether the list rel has field names or not.}
bool listRelHasFieldNames(AType t) {
    if (alrel(tls) := \unwrapType(t)) return size(tls) == size([ti | ti:alabel(_,_) <- tls]);
    throw "listRelHasFieldNames given non-List-Relation type <prettyPrintAType(t)>";
}

@doc{Get the field names of the list rel fields.}
public list[str] getListRelFieldNames(AType t) {
    if (alrel(tls) := unwrapType(t) && listRelHasFieldNames(t)) return [ l | alabel(l,_) <- tls ];
    if (alrel(_) := unwrapType(t)) throw "getListRelFieldNames given lrel type without field names: <prettyPrintAType(t)>";        
    throw "getListRelFieldNames given non-List-Relation type <prettyPrintAType(t)>";
}

@doc{Get the fields of a list relation.}
public list[Symbol] getListRelFields(AType t) {
    if (alrel(tls) := unwrapType(t)) return tls;
    if (alist(atuple(tls)) := unwrapType(t)) return tls;
    throw "getListRelFields given non-List-Relation type <prettyPrintAType(t)>";
}

@doc{Get the name of a type variable.}
str getTypeVarName(AType t) {
    if (aalias(_,_,Symbol at) := t) return getTypeVarName(at);
    if (alabel(_,Symbol lt) := t) return getTypeVarName(lt);
    if (aparameter(tvn,_) := t) return tvn;
    throw "getTypeVarName given unexpected type: <prettyPrintAType(t)>";
}

@doc{Get the bound of a type variable.}
public Symbol getTypeVarBound(AType t) {
    if (aalias(_,_,Symbol at) := t) return getTypeVarBound(at);
    if (alabel(_,Symbol lt) := t) return getTypeVarBound(lt);
    if (aparameter(_,tvb) := t) return tvb;
    throw "getTypeVarBound given unexpected type: <prettyPrintAType(t)>";
}

@doc{Get all the type variables inside a given type.}
public set[Symbol] collectTypeVars(AType t) {
    return { rt | / Symbol rt : aparameter(_,_) := t };
}

@doc{Provide an initial type map from the variables in the type to void.}
public map[str,Symbol] initializeTypeVarMap(AType t) {
    set[Symbol] rt = collectTypeVars(t);
    return ( getTypeVarName(tv) : makeVoidType() | tv <- rt );
}

@doc{See if a type contains any type variables.}
bool typeContainsTypeVars(AType t) = size(collectTypeVars(t)) > 0;

@doc{Return the names of all type variables in the given type.}
public set[str] typeVarNames(AType t) {
    return { tvn | aparameter(tvn,_) <- collectTypeVars(t) };
}

//
// Instantiate type variables based on a var name to type mapping.
//
// NOTE: We assume that bounds have already been checked, so this should not violate the bounds
// given on bounded type variables.
//
// NOTE: Commented out for now. Unfortunately, the visit could change some things that we normally
// would not change, so we need to instead do this using standard recursion. It is now in SubTypes
// along with the functionality which finds the mappings.
//public RType instantiateVars(map[RName,RType] varMappings, RType rt) {
//  return visit(rt) {
//      case RTypeVar(RFreeTypeVar(n)) : if (n in varMappings) insert(varMappings[n]);
//      case RTypeVar(RBoundTypeVar(n,_)) : if (n in varMappings) insert(varMappings[n]);   
//  };
//}

@doc{Get a list of arguments for the function.}
public list[Symbol] getFunctionArgumentTypes(AType ft) {
    if (afunc(_, ats, _) := unwrapType(ft)) return ats;
    if (afunc(_, ats) := unwrapType(ft)) return ats;
    throw "Cannot get function arguments from non-function type <prettyPrintAType(ft)>";
}

@doc{Get the arguments for a function in the form of a tuple.}
public Symbol getFunctionArgumentTypesAsTuple(AType ft) {
    if (afunc(_, ats, _) := unwrapType(ft)) return atuple(ats);
     if (afunc(_, ats) := unwrapType(ft)) return atuple(ats);
    throw "Cannot get function arguments from non-function type <prettyPrintAType(ft)>";
}

@doc{Get the return type for a function.}
public Symbol getFunctionReturnType(AType ft) {
    if (afunc(rt, _, _) := unwrapType(ft)) return rt;
    if (afunc(rt, _) := unwrapType(ft)) return rt; 
    throw "Cannot get function return type from non-function type <prettyPrintAType(ft)>";
}

@doc{Indicate if the given tuple has a field of the given name.}
bool tupleHasField(AType t, str fn) {
    return atuple(tas) := unwrapType(t) && fn in { l | alabel(l,_) <- tas } ;
}

@doc{Indicate if the given tuple has a field with the given field offset.}
bool tupleHasField(AType t, int fn) {
    return atuple(tas) := unwrapType(t) && 0 <= fn && fn < size(tas);
}

@doc{Get the type of the tuple field with the given name.}
public Symbol getTupleFieldType(AType t, str fn) {
    if (atuple(tas) := unwrapType(t)) {
        fieldmap = ( l : ltype | alabel(l,ltype) <- tas );
        if (fn in fieldmap) return fieldmap[fn];
        throw "Tuple <prettyPrintAType(t)> does not have field <fn>";
    }
    throw "getTupleFieldType given unexpected type <prettyPrintAType(t)>";
}

@doc{Get the type of the tuple field at the given offset.}
public Symbol getTupleFieldType(AType t, int fn) {
    if (atuple(tas) := unwrapType(t)) {
        if (0 <= fn && fn < size(tas)) return unwrapType(tas[fn]);
        throw "Tuple <prettyPrintAType(t)> does not have field <fn>";
    }
    throw "getTupleFieldType given unexpected type <prettyPrintAType(t)>";
}

@doc{Get the types of the tuple fields, with labels removed}
public list[Symbol] getTupleFieldTypes(AType t) {
    if (atuple(tas) := unwrapType(t))
        return [ (alabel(_,v) := li) ? v : li | li <- tas ];
    throw "Cannot get tuple field types from type <prettyPrintAType(t)>"; 
}

@doc{Get the fields of a tuple as a list.}
public list[Symbol] getTupleFields(AType t) {
    if (atuple(tas) := unwrapType(t)) return tas;
    throw "Cannot get tuple fields from type <prettyPrintAType(t)>"; 
}

@doc{Get the number of fields in a tuple.}
public int getTupleFieldCount(AType t) = size(getTupleFields(t));

@doc{Does this tuple have field names?}
bool tupleHasFieldNames(AType t) {
    if (atuple(tas) := unwrapType(t)) return size(tas) == size({ti|ti:alabel(_,_) <- tas});
    throw "tupleHasFieldNames given non-Tuple type <prettyPrintAType(t)>";
}

@doc{Get the names of the tuple fields.}
public list[str] getTupleFieldNames(AType t) {
    if (atuple(tls) := unwrapType(t)) {
        if (tupleHasFieldNames(t)) {
            return [ l | alabel(l,_) <- tls ];
        }
        throw "getTupleFieldNames given tuple type without field names: <prettyPrintAType(t)>";        
    }
    throw "getTupleFieldNames given non-Tuple type <prettyPrintAType(t)>";
}

@doc{Get the name of the tuple field at the given offset.}
str getTupleFieldName(AType t, int idx) {
    list[str] names = getTupleFieldNames(t);
    if (0 <= idx && idx < size(names)) return names[idx];
    throw "getTupleFieldName given invalid index <idx>";
}

@doc{Get the element type of a set.}
public Symbol getSetElementType(AType t) {
    if (aset(et) := unwrapType(t)) return et;
    if (arel(ets) := unwrapType(t)) return atuple(ets);
    throw "Error: Cannot get set element type from type <prettyPrintAType(t)>";
}

@doc{Get the element type of a bag.}
public Symbol getBagElementType(AType t) {
    if (abag(et) := unwrapType(t)) return et;
    throw "Error: Cannot get set element type from type <prettyPrintAType(t)>";
}

@doc{Get the domain and range of the map as a tuple.}
public Symbol getMapFieldsAsTuple(AType t) {
    if (amap(dt,rt) := unwrapType(t)) return atuple([dt,rt]);
    throw "getMapFieldsAsTuple called with unexpected type <prettyPrintAType(t)>";
}       

@doc{Check to see if a map defines a field (by name).}
bool mapHasField(AType t, str fn) = tupleHasField(getMapFieldsAsTuple(t),fn);

@doc{Check to see if a map defines a field (by index).}
bool mapHasField(AType t, int fn) = tupleHasField(getMapFieldsAsTuple(t),fn);

@doc{Return the type of a field defined on a map (by name).}
public Symbol getMapFieldType(AType t, str fn) = getTupleFieldType(getMapFieldsAsTuple(t),fn);

@doc{Return the type of a field defined on a map (by index).}
public Symbol getMapFieldType(AType t, int fn) = getTupleFieldType(getMapFieldsAsTuple(t),fn);

@doc{Get the fields in a map as a list of fields.}
public list[Symbol] getMapFields(AType t) = getTupleFields(getMapFieldsAsTuple(t));

@doc{Check to see if the map has field names.}
bool mapHasFieldNames(AType t) = tupleHasFieldNames(getMapFieldsAsTuple(t));

@doc{Get the field names from the map fields.}
public tuple[str domainName, str rangeName] getMapFieldNames(AType t) {
    if (mapHasFieldNames(t),[alabel(l1,_),alabel(l2,_)] := getMapFields(t)) {
        return < l1, l2 >;
    }
    throw "getMapFieldNames given map type without field names: <prettyPrintAType(t)>";        
}

@doc{Get the field name for the field at a specific index.}
str getMapFieldName(AType t, int idx) = getMapFieldNames(t)[idx];

@doc{Get the domain type of the map.}    
public Symbol getMapDomainType(AType t) = unwrapType(getMapFields(t)[0]);

@doc{Get the range type of the map.}
public Symbol getMapRangeType(AType t) = unwrapType(getMapFields(t)[1]);

@doc{Get a list of the argument types in a constructor.}
public list[Symbol] getConstructorArgumentTypes(AType ct) {
    if (acons(_,_,cts) := unwrapType(ct)) return cts;
    throw "Cannot get constructor arguments from non-constructor type <prettyPrintAType(ct)>";
}

@doc{Get a tuple with the argument types as the fields.}
public Symbol getConstructorArgumentTypesAsTuple(AType ct) {
    return atuple(getConstructorArgumentTypes(ct));
}

@doc{Get the ADT type of the constructor.}
public Symbol getConstructorResultType(AType ct) {
    if (acons(a,_,_) := unwrapType(ct)) return a;
    throw "Cannot get constructor ADT type from non-constructor type <prettyPrintAType(ct)>";
}

@doc{Get the element type of a list.}
public Symbol getListElementType(AType t) {
    if (alist(et) := unwrapType(t)) return et;
    if (alrel(ets) := unwrapType(t)) return atuple(ets);    
    throw "Error: Cannot get list element type from type <prettyPrintAType(t)>";
}

@doc{Get the name of the ADT.}
str getADTName(AType t) {
    if (\adt(n,_) := unwrapType(t)) return n;
    if (acons(a,_,_) := unwrapType(t)) return getADTName(a);
    if (areified(_) := unwrapType(t)) return "type";
    throw "getADTName, invalid type given: <prettyPrintAType(t)>";
}

@doc{Get the type parameters of an ADT.}
public list[Symbol] getADTTypeParameters(AType t) {
    if (\adt(n,ps) := unwrapType(t)) return ps;
    if (acons(a,_,_) := unwrapType(t)) return getADTTypeParameters(a);
    if (areified(_) := unwrapType(t)) return [];
    throw "getADTTypeParameters given non-ADT type <prettyPrintAType(t)>";
}

@doc{Return whether the ADT has type parameters.}
bool adtHasTypeParameters(AType t) = size(getADTTypeParameters(t)) > 0;

@doc{Get the name of a user type.}
str getUserTypeName(AType ut) {
    if (\user(x,_) := unwrapType(ut)) return prettyPrintName(x);
    throw "Cannot get user type name from non user type <prettyPrintAType(ut)>";
} 

@doc{Get the type parameters from a user type.}
public list[Symbol] getUserTypeParameters(AType ut) {
    if (\user(_,ps) := unwrapType(ut)) return ps;
    throw "Cannot get type parameters from non user type <prettyPrintAType(ut)>";
}

@doc{Does this user type have type parameters?}
bool userTypeHasParameters(AType ut) = size(getUserTypeParameters(ut)) > 0;

@doc{Get the name of the type alias.}
str getAliasName(AType t) {
    if (aalias(x,_,_) := t) return x;
    throw "Cannot get the alias name from non alias type <prettyPrintAType(t)>";
}

@doc{Get the aliased type of the type alias.}
public Symbol getAliasedType(AType t) {
    if (aalias(_,_,at) := t) return at;
    throw "Cannot get the aliased type from non alias type <prettyPrintAType(t)>";
}

@doc{Get the type parameters for the alias.}
public list[Symbol] getAliasTypeParameters(AType t) {
    if (aalias(_,ps,_) := t) return ps;
    throw "getAliasTypeParameters given non-alias type <prettyPrintAType(t)>";
}

@doc{Does this alias have type parameters?}
bool aliasHasTypeParameters(AType t) = size(getAliasTypeParameters(t)) > 0;

@doc{Unwind any aliases inside a type.}
public Symbol unwindAliases(AType t) {
    solve(t) {
        t = visit(t) { case aalias(tl,ps,tr) => tr };
    }
    return t;
}

@doc{Is the provided type a failure type?}
bool isFailType(failure(_)) = true;
public default bool isFailType(Symbol _) = false;

@doc{Construct a new fail type with the given message and error location.}
public Symbol makeFailType(str s, loc l) = failure({error(s,l)});

@doc{Construct a new fail type with the given message and error location.}
public Symbol makeFailTypeAsWarning(str s, loc l) = failure({warning(s,l)});

@doc{Get the failure messages out of the type.}
public set[Message] getFailures(failure(set[Message] ms)) = ms;

@doc{Extend a failure type with new failure messages.}
public Symbol extendFailType(failure(set[Message] ms), set[Message] msp) = failure(ms + msp);
public default Symbol extendFailType(Symbol t) {    
    throw "Cannot extend a non-failure type with failure information, type <prettyPrintAType(t)>";
}

@doc{Collapse a set of failure types into a single failure type with all the failures included.} 
public Symbol collapseFailTypes(set[Symbol] rt) = failure({ s | failure(ss) <- rt, s <- ss }); 

@doc{Is this type an inferred type?}
bool isInferredType(\inferred(_)) = true;
public default bool isInferredType(Symbol _) = false;

@doc{Does this type have an inferred type?}
bool hasInferredType(Symbol \type) = (/\inferred(_) := \type);

@doc{Construct a new inferred type.}
public Symbol makeInferredType(int n) = \inferred(n);

@doc{Get the numeric identifier for the inferred type.}
public int getInferredTypeIndex(Symbol t) {
    if (\inferred(n) := t) return n;
    throw "Error: Cannot get inferred type index from non-inferred type <prettyPrintAType(t)>";
}

@doc{Is this type an overloaded type?}
bool isOverloadedType(\overloaded(_,_)) = true;
public default bool isOverloadedType(Symbol _) = false;

@doc{Get the non-default overloads stored inside the overloaded type.}
public set[Symbol] getNonDefaultOverloadOptions(Symbol t) {
    if (\overloaded(s,_) := t) return s;
    throw "Error: Cannot get non-default overloaded options from non-overloaded type <prettyPrintAType(t)>";
}

@doc{Get the default overloads stored inside the overloaded type.}
public set[Symbol] getDefaultOverloadOptions(Symbol t) {
    if (\overloaded(_,defaults) := t) return defaults;
    throw "Error: Cannot get default overloaded options from non-overloaded type <prettyPrintAType(t)>";
}

@doc{Construct a new overloaded type.}
public Symbol makeOverloadedType(set[Symbol] options, set[Symbol] defaults) {
    options  = { *( (\overloaded(opts,_) := optItem) ? opts : { optItem } ) | optItem <- options };
    defaults = defaults + { *( (\overloaded(_,opts) := optItem) ? opts : {} ) | optItem <- options };
    return \overloaded(options,defaults);
}

@doc{Ensure that sets of tuples are treated as relations.}
public Symbol aset(Symbol t) = arel(getTupleFields(t)) when isTupleType(t);

@doc{Ensure that lists of tuples are treated as list relations.}
public Symbol alist(Symbol t) = alrel(getTupleFields(t)) when isTupleType(t);

@doc{Calculate the lub of a list of types.}
public Symbol lubList(list[Symbol] ts) {
    Symbol theLub = avoid();
    for (t <- ts) theLub = lub(theLub,t);
    return theLub;
}

@doc{Is this type a non-container type?}
bool isElementType(Symbol t) = 
    isIntType(t) || isBoolType(t) || isRealType(t) || isRatType(t) || isStrType(t) || 
    isNumType(t) || isNodeType(t) || isVoidType(t) || isValueType(t) || isLocType(t) || 
    isDateTimeType(t) || isTupleType(t) || isADTType(t) || isConstructorType(t) ||
    isFunctionType(t) || isReifiedType(t) || isNonTerminalType(t);

@doc{Is this type a container type?}
bool isContainerType(Symbol t) =
    isSetType(t) || isListType(t) || isMapType(t) || isBagType(t);
    
@doc{Synopsis: Determine if the given type is a nonterminal.}
bool isNonTerminalType(aalias(_,_,Symbol at)) = isNonTerminalType(at);
bool isNonTerminalType(aparameter(_,Symbol tvb)) = isNonTerminalType(tvb);
bool isNonTerminalType(alabel(_,Symbol lt)) = isNonTerminalType(lt);
bool isNonTerminalType(Symbol::\start(Symbol ss)) = isNonTerminalType(ss);
bool isNonTerminalType(Symbol::\conditional(Symbol ss,_)) = isNonTerminalType(ss);
bool isNonTerminalType(Symbol::\sort(_)) = true;
bool isNonTerminalType(Symbol::\lex(_)) = true;
bool isNonTerminalType(Symbol::\layouts(_)) = true;
bool isNonTerminalType(Symbol::\keywords(_)) = true;
bool isNonTerminalType(Symbol::\aparameterized-sort(_,_)) = true;
bool isNonTerminalType(Symbol::\aparameterized-lex(_,_)) = true;
bool isNonTerminalType(Symbol::\iter(_)) = true;
bool isNonTerminalType(Symbol::\iter-star(_)) = true;
bool isNonTerminalType(Symbol::\iter-seps(_,_)) = true;
bool isNonTerminalType(Symbol::\iter-star-seps(_,_)) = true;
bool isNonTerminalType(Symbol::\empty()) = true;
bool isNonTerminalType(Symbol::\opt(_)) = true;
bool isNonTerminalType(Symbol::\alt(_)) = true;
bool isNonTerminalType(Symbol::\seq(_)) = true;

public default bool isNonTerminalType(Symbol _) = false;    

bool isNonTerminalIterType(aalias(_,_,Symbol at)) = isNonTerminalIterType(at);
bool isNonTerminalIterType(aparameter(_,Symbol tvb)) = isNonTerminalIterType(tvb);
bool isNonTerminalIterType(alabel(_,Symbol lt)) = isNonTerminalIterType(lt);
bool isNonTerminalIterType(Symbol::\iter(_)) = true;
bool isNonTerminalIterType(Symbol::\iter-star(_)) = true;
bool isNonTerminalIterType(Symbol::\iter-seps(_,_)) = true;
bool isNonTerminalIterType(Symbol::\iter-star-seps(_,_)) = true;
public default bool isNonTerminalIterType(Symbol _) = false;    

public Symbol getNonTerminalIterElement(aalias(_,_,Symbol at)) = getNonTerminalIterElement(at);
public Symbol getNonTerminalIterElement(aparameter(_,Symbol tvb)) = getNonTerminalIterElement(tvb);
public Symbol getNonTerminalIterElement(alabel(_,Symbol lt)) = getNonTerminalIterElement(lt);
public Symbol getNonTerminalIterElement(Symbol::\iter(Symbol i)) = i;
public Symbol getNonTerminalIterElement(Symbol::\iter-star(Symbol i)) = i;
public Symbol getNonTerminalIterElement(Symbol::\iter-seps(Symbol i,_)) = i;
public Symbol getNonTerminalIterElement(Symbol::\iter-star-seps(Symbol i,_)) = i;
public default Symbol getNonTerminalIterElement(Symbol i) {
    throw "<prettyPrintAType(i)> is not an iterable non-terminal type";
}   

bool isNonTerminalOptType(aalias(_,_,Symbol at)) = isNonTerminalOptType(at);
bool isNonTerminalOptType(aparameter(_,Symbol tvb)) = isNonTerminalOptType(tvb);
bool isNonTerminalOptType(alabel(_,Symbol lt)) = isNonTerminalOptType(lt);
bool isNonTerminalOptType(Symbol::\opt(Symbol ot)) = true;
public default bool isNonTerminalOptType(Symbol _) = false;

public Symbol getNonTerminalOptType(aalias(_,_,Symbol at)) = getNonTerminalOptType(at);
public Symbol getNonTerminalOptType(aparameter(_,Symbol tvb)) = getNonTerminalOptType(tvb);
public Symbol getNonTerminalOptType(alabel(_,Symbol lt)) = getNonTerminalOptType(lt);
public Symbol getNonTerminalOptType(Symbol::\opt(Symbol ot)) = ot;
public default Symbol getNonTerminalOptType(Symbol ot) {
    throw "<prettyPrintAType(ot)> is not an optional non-terminal type";
}

bool isStartNonTerminalType(aalias(_,_,Symbol at)) = isNonTerminalType(at);
bool isStartNonTerminalType(aparameter(_,Symbol tvb)) = isNonTerminalType(tvb);
bool isStartNonTerminalType(alabel(_,Symbol lt)) = isNonTerminalType(lt);
bool isStartNonTerminalType(Symbol::\start(_)) = true;
public default bool isStartNonTerminalType(Symbol _) = false;    

public Symbol getStartNonTerminalType(aalias(_,_,Symbol at)) = getStartNonTerminalType(at);
public Symbol getStartNonTerminalType(aparameter(_,Symbol tvb)) = getStartNonTerminalType(tvb);
public Symbol getStartNonTerminalType(alabel(_,Symbol lt)) = getStartNonTerminalType(lt);
public Symbol getStartNonTerminalType(Symbol::\start(Symbol s)) = s;
public default Symbol getStartNonTerminalType(Symbol s) {
    throw "<prettyPrintAType(s)> is not a start non-terminal type";
}

@doc{Get the name of the nonterminal.}
str getNonTerminalName(aalias(_,_,Symbol at)) = getNonTerminalName(at);
str getNonTerminalName(aparameter(_,Symbol tvb)) = getNonTerminalName(tvb);
str getNonTerminalName(alabel(_,Symbol lt)) = getNonTerminalName(lt);
str getNonTerminalName(Symbol::\start(Symbol ss)) = getNonTerminalName(ss);
str getNonTerminalName(Symbol::\sort(str n)) = n;
str getNonTerminalName(Symbol::\lex(str n)) = n;
str getNonTerminalName(Symbol::\layouts(str n)) = n;
str getNonTerminalName(Symbol::\keywords(str n)) = n;
str getNonTerminalName(Symbol::\aparameterized-sort(str n,_)) = n;
str getNonTerminalName(Symbol::\aparameterized-lex(str n,_)) = n;
str getNonTerminalName(Symbol::\iter(Symbol ss)) = getNonTerminalName(ss);
str getNonTerminalName(Symbol::\iter-star(Symbol ss)) = getNonTerminalName(ss);
str getNonTerminalName(Symbol::\iter-seps(Symbol ss,_)) = getNonTerminalName(ss);
str getNonTerminalName(Symbol::\iter-star-seps(Symbol ss,_)) = getNonTerminalName(ss);
str getNonTerminalName(Symbol::\opt(Symbol ss)) = getNonTerminalName(ss);
str getNonTerminalName(Symbol::\conditional(Symbol ss,_)) = getNonTerminalName(ss);
public default str getNonTerminalName(Symbol s) { throw "Invalid nonterminal passed to getNonTerminalName: <s>"; }

//@doc{Check to see if the type allows fields.}
//bool nonTerminalAllowsFields(aalias(_,_,Symbol at)) = nonTerminalAllowsFields(at);
//bool nonTerminalAllowsFields(aparameter(_,Symbol tvb)) = nonTerminalAllowsFields(tvb);
//bool nonTerminalAllowsFields(alabel(_,Symbol lt)) = nonTerminalAllowsFields(lt);
//bool nonTerminalAllowsFields(Symbol::\start(Symbol ss)) = true;
//bool nonTerminalAllowsFields(Symbol::\sort(str n)) = true;
//bool nonTerminalAllowsFields(Symbol::\lex(str n)) = true;
//bool nonTerminalAllowsFields(Symbol::aparameterized-sort(str n,_)) = true;
//bool nonTerminalAllowsFields(Symbol::aparameterized-lex(str n,_)) = true;
//bool nonTerminalAllowsFields(Symbol::\opt(Symbol ss)) = true;
//bool nonTerminalAllowsFields(Symbol::\conditional(Symbol ss,_)) = nonTerminalAllowsFields(ss);
//public default bool nonTerminalAllowsFields(Symbol s) = false;

@doc{Get the type parameters of a nonterminal.}
//public list[Symbol] getNonTerminalTypeParameters(Symbol t) = [ rt | / Symbol rt : aparameter(_,_) := t ];
public list[Symbol] getNonTerminalTypeParameters(Symbol t) {
    t = unwrapType(t);
    if (Symbol::aparameterized-sort(n,ps) := t) return ps;
    if (Symbol::aparameterized-lex(n,ps) := t) return ps;
    if (Symbol::\start(s) := t) return getNonTerminalTypeParameters(s);
    if (Symbol::\iter(s) := t) return getNonTerminalTypeParameters(s);
    if (Symbol::\iter-star(s) := t) return getNonTerminalTypeParameters(s);
    if (Symbol::\iter-seps(s,_) := t) return getNonTerminalTypeParameters(s);
    if (Symbol::\iter-star-seps(s,_) := t) return getNonTerminalTypeParameters(s);
    if (Symbol::\opt(s) := t) return getNonTerminalTypeParameters(s);
    if (Symbol::\conditional(s,_) := t) return getNonTerminalTypeParameters(s);
    if (Symbol::\prod(s,_,_,_) := t) return getNonTerminalTypeParameters(s);
    return [ ];
}

public Symbol provideNonTerminalTypeParameters(Symbol t, list[Symbol] ps) {
    // Note: this function assumes the length is proper -- that we are replacing
    // a list of params with a list of types that is the same length. The caller
    // needs to check this.
    
    t = unwrapType(t);
    
    if (Symbol::aparameterized-sort(n,ts) := t) return t[parameters=ps];
    if (Symbol::aparameterized-lex(n,ts) := t) return t[parameters=ps];
    if (Symbol::\start(s) := t) return t[symbol=provideNonTerminalTypeParameters(s,ps)];
    if (Symbol::\iter(s) := t) return t[symbol=provideNonTerminalTypeParameters(s,ps)];
    if (Symbol::\iter-star(s) := t) return t[symbol=provideNonTerminalTypeParameters(s,ps)];
    if (Symbol::\iter-seps(s,_) := t) return t[symbol=provideNonTerminalTypeParameters(s,ps)];
    if (Symbol::\iter-star-seps(s,_) := t) return t[symbol=provideNonTerminalTypeParameters(s,ps)];
    if (Symbol::\opt(s) := t) return t[symbol=provideNonTerminalTypeParameters(s,ps)];
    if (Symbol::\conditional(s,_) := t) return t[symbol=provideNonTerminalTypeParameters(s,ps)];
    if (Symbol::\prod(s,_,_,_) := t) return t[\sort=provideNonTerminalTypeParameters(s,ps)];
    return t;
}

@doc{Synopsis: Determine if the given type is a production.}
bool isProductionType(aalias(_,_,Symbol at)) = isProductionType(at);
bool isProductionType(aparameter(_,Symbol tvb)) = isProductionType(tvb);
bool isProductionType(alabel(_,Symbol lt)) = isProductionType(lt);
bool isProductionType(Symbol::\prod(_,_,_,_)) = true;
public default bool isProductionType(Symbol _) = false; 

public Symbol removeConditional(conditional(Symbol s, set[Condition] _)) = s;
public Symbol removeConditional(label(str lab, conditional(Symbol s, set[Condition] _)))
  = label(lab, s);
public default Symbol removeConditional(Symbol s) = s;

@doc{Get a list of the argument types in a production.}
public list[Symbol] getProductionArgumentTypes(Symbol pr) {
    if (Symbol::\prod(_,_,ps,_) := unwrapType(pr)) {
        return [ removeConditional(psi) | psi <- ps, isNonTerminalType(psi) ] ;
    }
    throw "Cannot get production arguments from non-production type <prettyPrintAType(pr)>";
}

@doc{Get a tuple with the argument types as the fields.}
public Symbol getProductionArgumentTypesAsTuple(Symbol pr) {
    return atuple(getProductionArgumentTypes(pr));
}

@doc{Get the sort type of the production.}
public Symbol getProductionSortType(Symbol pr) {
    if (Symbol::\prod(s,_,_,_) := unwrapType(pr)) return s;
    throw "Cannot get production sort type from non-production type <prettyPrintAType(pr)>";
}

bool hasDeferredTypes(Symbol t) = size({d | /d:deferred(_) := t}) > 0;

bool subtype(Symbol::deferred(Symbol t), Symbol s) = subtype(t,s);
bool subtype(Symbol t, Symbol::deferred(Symbol s)) = subtype(t,s); 
bool subtype(Symbol t, Symbol::\adt("Tree",[])) = true when isNonTerminalType(t);
bool subtype(Symbol t, Symbol::anode()) = true when isNonTerminalType(t);
bool subtype(Symbol::\iter-seps(Symbol s, list[Symbol] seps), Symbol::\iter-star-seps(Symbol t, list[Symbol] seps2)) = subtype(s,t) && subtype(seps, seps2);
bool subtype(Symbol::\iter(Symbol s), Symbol::\iter-star(Symbol t)) = subtype(s, t);
// TODO: add subtype for elements under optional and alternative, but that would also require auto-wrapping/unwrapping in the run-time
// bool subtype(Symbol s, \opt(Symbol t)) = subtype(s,t);
// bool subtype(Symbol s, \alt({Symbol t, *_}) = true when subtype(s, t); // backtracks over the alternatives

