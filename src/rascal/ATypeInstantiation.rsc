

@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Jurgen J. Vinju - Jurgen.Vinju@cwi.nl - CWI}
@contributor{Mark Hills - Mark.Hills@cwi.nl (CWI)}
@contributor{Paul Klint - Paul Klint@cwi.nl (CWI)}
module rascal::ATypeInstantiation

import Set;
import IO;
import Node;

//import lang::rascal::types::AbstractName;
//import lang::rascal::types::AbstractType;
import rascal::ATypeExceptions;

import rascal::AType;
import rascal::ATypeUtils;
import typepal::ExtractFRModel;

public alias Bindings = map[str varName, AType varType];

// TODO: Add support for bags if we ever get around to supporting them...
// TODO: Add support for overloaded types if they can make it to here (this is
// usually invoked on specific types that are inside overloads)
public Bindings match(AType r, AType s, Bindings b, bool bindIdenticalVars=false) {
    if (!typeContainsTypeVars(r)) return b;
    return match(r,s,b,bindIdenticalVars);
}

public Bindings match(AType r, AType s, Bindings b, bool bindIdenticalVars) {
    // Strip off labels and aliases
    if (alabel(_, lt) := r) return match(lt, s, b, bindIdenticalVars);
    if (alabel(_, rt) := s) return match(r, rt, b, bindIdenticalVars);
    if (aalias(_,_,lt) := r) return match(lt, s, b, bindIdenticalVars);
    if (aalias(_,_,rt) := s) return match(r, rt, b, bindIdenticalVars);

    // The simple case: if the receiver is a basic type or a node 
    // (i.e., has no internal structure), just do a comparability
    // check. The receiver obviously does not contain a parameter.
    if (arity(r) == 0 && comparable(s,r)) return b;

    // Another simple case: if the receiver has no type vars, then just return
    // the current bindings.
    if (!typeContainsTypeVars(r)) return b;
        
    // Handle parameters
    if (isTypeVar(r) && isTypeVar(s) && getTypeVarName(r) == getTypeVarName(s) && getTypeVarBound(r) == getTypeVarBound(s) && !bindIdenticalVars) {
        return b;
    }
    
    if (isTypeVar(r)) {
        varName = getTypeVarName(r);
        varBound = getTypeVarBound(r);
        
        if (varName in b) {
            lubbed = lub(s, b[varName]);
            if (!asubtype(lubbed, varBound))
                throw invalidMatch(varName, lubbed, varBound);
            b[varName] = lubbed;
        } else {
            b[varName] = s;
        }
        
        return b;
    }
        
    // For sets and relations, check to see if the "contents" are
    // able to be matched to one another
    if ( isSetType(r) && isSetType(s) ) {
        if ( isRelType(r) && isVoidType(getSetElementType(s)) ) {
            return match(getSetElementType(r), atuple([\void() | idx <- index(getRelFields(r))]), b, bindIdenticalVars);
        } else if ( isVoidType(getSetElementType(s)) ) {
            return b;
        } else {    
            return match(getSetElementType(r), getSetElementType(s), b, bindIdenticalVars);
        }
    }
        
    // For lists and list relations, check to see if the "contents" are
    // able to be matched to one another
    if ( isListType(r) && isListType(s) ) {
        if ( isListRelType(r) && isVoidType(getListElementType(s)) ) {
            return match(getListElementType(r), atuple([\void() | idx <- index(getListRelFields(r))]), b, bindIdenticalVars);
        } else if ( isVoidType(getListElementType(s)) ) {
            return b;
        } else {
            return match(getListElementType(r), getListElementType(s), b, bindIdenticalVars);
        }
    }
        
    // For maps, match the domains and ranges
    if ( isMapType(r) && isMapType(s) )
        return match(getMapFieldsAsTuple(r), getMapFieldsAsTuple(s), b, bindIdenticalVars);
    
    // For reified types, match the type being reified
    if ( isReifiedType(r) && isReifiedType(s) )
        return match(getReifiedType(r), getReifiedType(s), b, bindIdenticalVars);

    // For ADTs, try to match parameters when the ADTs are the same
    if ( isADTType(r) && isADTType(s) && getADTName(r) == getADTName(s) && size(getADTTypeParameters(r)) == size(getADTTypeParameters(s))) {
        rparams = getADTTypeParameters(r);
        sparams = getADTTypeParameters(s);
        for (idx <- index(rparams)) b = match(rparams[idx], sparams[idx], b, bindIdenticalVars);
        return b;
    }
            
    // For constructors, match when the constructor name, ADT name, and arity are the same, then we can check params
    if ( isConstructorType(r) && isConstructorType(s) && getADTName(r) == getADTName(s)) {
        b = match(getConstructorArgumentTypesAsTuple(r), getConstructorArgumentTypesAsTuple(s), b, bindIdenticalVars);
        return match(getConstructorResultType(r), getConstructorResultType(s), b, bindIdenticalVars);
    }
    
    if ( isConstructorType(r) && isADTType(s) ) {
        return match(getConstructorResultType(r), s, b, bindIdenticalVars);
    }
    
    // For functions, match the return types and the parameter types
    if ( isFunctionType(r) && isFunctionType(s) ) {
        b = match(getFunctionArgumentTypesAsTuple(r), getFunctionArgumentTypesAsTuple(s), b, bindIdenticalVars);
        return match(getFunctionReturnType(r), getFunctionReturnType(s), b, bindIdenticalVars);
    }
    
    // For tuples, check the arity then match the item types
    if ( isTupleType(r) && isTupleType(s) && getTupleFieldCount(r) == getTupleFieldCount(s) ) {
        rfields = getTupleFieldTypes(r);
        sfields = getTupleFieldTypes(s);
        for (idx <- index(rfields)) {
            if (!isVoidType(sfields[idx])) {
                b = match(rfields[idx], sfields[idx], b, bindIdenticalVars);
            }
        }
        return b;
    }
    
    throw invalidMatch(r, s);
}

@doc{Instantiate type parameters found inside the types.}
AType instantiate(AType atype, Bindings bindings, Tree where){
    return visit(atype){
        case aparameter(str pname, AType bound): {
             if(pname in bindings){
                actual = bindings[pname];
                if(asubtype(actual, bound)) insert actual;  
                reportError(v, "Type parameter <fmt(pname)> should be less than <fmt(bound)>, but is bound to <fmt(actual)>");
                throw invalidInstantiation();  
             } else {
                reportError(where, "Type parameter <fmt(pname)> unbound");
                throw invalidInstantiation();
             }
        }
    }
}

//AType instantiate(AType t:\void(), Bindings bindings) = t;
//AType instantiate(AType::alabel(str x, AType t), Bindings bindings) = AType::alabel(x, instantiate(t,bindings));
//AType instantiate(AType::aset(AType et), Bindings bindings) = makeSetType(instantiate(et,bindings));
//AType instantiate(AType::arel(list[AType] ets), Bindings bindings) = AType::arel([ instantiate(et,bindings) | et <- ets ]);
//AType instantiate(AType::atuple(list[AType] ets), Bindings bindings) = AType::atuple([ instantiate(et,bindings) | et <- ets ]);
//AType instantiate(AType::alist(AType et), Bindings bindings) = makeListType(instantiate(et,bindings));
//AType instantiate(AType::alrel(list[AType] ets), Bindings bindings) = AType::alrel([ instantiate(et,bindings) | et <- ets ]);
//AType instantiate(AType::amap(AType md, AType mr), Bindings bindings) = AType::amap(instantiate(md,bindings), instantiate(mr,bindings));
//AType instantiate(AType::abag(AType et), Bindings bindings) = AType::abag(instantiate(et,bindings));
//AType instantiate(AType::aparameter(str s, AType t), Bindings bindings) = bindings[s] when s in bindings && asubtype(bindings[s],t);
//AType instantiate(AType::aparameter(str s, AType t), Bindings bindings) = invalidInstantiation() when s in bindings && !asubtype(bindings[s],t);
//AType instantiate(AType pt:aparameter(str s, AType t), Bindings bindings) = pt when s notin bindings;
//AType instantiate(AType::aadt(str s, list[AType] ps), Bindings bindings) = AType::aadt(s,[instantiate(p,bindings) | p <- ps]);
//AType instantiate(AType::acons(AType a, str name, list[AType] ps), Bindings bindings) = AType::acons(instantiate(a,bindings), name, [instantiate(p,bindings) | p <- ps]);
//AType instantiate(AType::aalias(str s, list[AType] ps, AType at), Bindings bindings) = AType::aalias(s, [instantiate(p,bindings) | p <- ps], instantiate(at,bindings));
//AType instantiate(AType::afunc(AType rt, list[AType] ps, list[AType] kws), Bindings bindings) = AType::afunc(instantiate(rt,bindings),[instantiate(p,bindings) | p <- ps], [instantiate(p,bindings) | p <- kws]);
////AType instantiate(\var-func(AType rt, list[AType] ps, AType va), Bindings bindings) = \var-func(instantiate(rt,bindings),[instantiate(p,bindings) | p <- ps],instantiate(va,bindings));
//AType instantiate(AType::areified(AType t), Bindings bindings) = AType::areified(instantiate(t,bindings));
//AType instantiate(AType::\aparameterized-sort(str n, list[AType] ts), Bindings bindings) = AType::aparameterized-sort(n, [instantiate(p,bindings) | p <- ts]);
//AType instantiate(AType::\aparameterized-lex(str n, list[AType] ts), Bindings bindings) = AType::aparameterized-lex(n, [instantiate(p,bindings) | p <- ts]);
//AType instantiate(AType::\start(AType s), Bindings bindings) = AType::\start(instantiate(s,bindings));
//AType instantiate(AType::\iter(AType s), Bindings bindings) = AType::\iter(instantiate(s,bindings));
//AType instantiate(AType::\iter-star(AType s), Bindings bindings) = AType::\iter-star(instantiate(s,bindings));
//AType instantiate(AType::\iter-seps(AType s, list[AType] seps), Bindings bindings) = AType::\iter-seps(instantiate(s,bindings),seps);
//AType instantiate(AType::\iter-star-seps(AType s, list[AType] seps), Bindings bindings) = AType::\iter-star-seps(instantiate(s,bindings),seps);
//AType instantiate(AType::\opt(AType s), Bindings bindings) = AType::\opt(instantiate(s,bindings));
//AType instantiate(AType::\conditional(AType s, set[Condition] conds), Bindings bindings) = AType::\conditional(instantiate(s,bindings),conds);
//AType instantiate(AType::\prod(AType s, str name, list[AType] parameters, set[Attr] attributes), Bindings bindings) = AType::\prod(instantiate(s,bindings),name,parameters,attributes);
//default AType instantiate(AType t, Bindings bindings) = t;