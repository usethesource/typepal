@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}

@contributor{Mark Hills - Mark.Hills@cwi.nl (CWI)}
@contributor{MPaul Klint - Paul.Klint@cwi.nl (CWI)}
module rascal::ConvertType

import Set;
import String;
import IO;
import Message;
//import Type;

extend typepal::AType;
extend rascal::AType;

import rascal::ATypeUtils;

import lang::rascal::types::AbstractName;

import lang::rascal::\syntax::Rascal;
import lang::rascal::grammar::definition::Symbols;

//@doc{Annotations for adding error and warning information to types}
//anno set[Message] Symbol@errinfo;

//@doc{Mark the location of the type in the source file}
//anno loc Symbol@at;

@doc{Convert from the concrete to the abstract representations of Rascal basic types.}
public tuple[set[Message], AType] convertBasicType(BasicType t) {
    switch(t) {
        case (BasicType)`bool` : return <{}, abool()>;
        case (BasicType)`int` : return <{}, aint()>;
        case (BasicType)`rat` : return <{}, arat()>;
        case (BasicType)`real` : return <{}, areal()>;
        case (BasicType)`num` : return <{}, anum()>;
        case (BasicType)`str` : return <{}, astr()>;
        case (BasicType)`value` : return <{}, avalue()>;
        case (BasicType)`node` : return <{}, anode()>;
        case (BasicType)`void` : return <{}, avoid()>;
        case (BasicType)`loc` : return <{}, aloc()>;
        case (BasicType)`datetime` : return <{}, adatetime()>;

        case (BasicType)`list` : 
            return <{ error("Non-well-formed type, type should have one type argument", t@\loc) }, alist(avoid())>;
        case (BasicType)`set` : 
            return <{ error("Non-well-formed type, type should have one type argument", t@\loc) }, aset(avoid())>;
        case (BasicType)`bag` : 
            return <{ error("Non-well-formed type, type should have one type argument", t@\loc) }, abag(avoid())>;
        case (BasicType)`map` : 
            return <{ error("Non-well-formed type, type should have two type arguments", t@\loc) }, amap(avoid(),avoid())>;
        case (BasicType)`rel` : 
            return <{ error("Non-well-formed type, type should have one or more type arguments", t@\loc) }, \rel([])>;
        case (BasicType)`lrel` : 
            return <{ error("Non-well-formed type, type should have one or more type arguments", t@\loc) }, alrel([])>;
        case (BasicType)`tuple` : 
            return <{ error("Non-well-formed type, type should have one or more type arguments", t@\loc) }, atuple([])>;
        case (BasicType)`type` : 
            return <{ error("Non-well-formed type, type should have one type argument", t@\loc) }, areified(avoid())>;
    }
}

@doc{Convert from the concrete to the abstract representations of Rascal type arguments.}
public tuple[set[Message], AType] convertTypeArg(TypeArg ta) {
    switch(ta) {
        case (TypeArg) `<Type t>` : return convertType(t);
        case (TypeArg) `<Type t> <Name n>` : {
            <msgs, tp> =convertType(t);
            return alabel(getSimpleName(convertName(n)), tp);
        }
    }
}

@doc{Convert lists of type arguments.}
public tuple[set[Message], list[AType]] convertTypeArgList({TypeArg ","}* tas) {
    msgs = {};
    types =
        for(ta <- tas){
            <msgs1, tp> = convertTypeArg(ta);
            msgs += msgs1;
            append tp;
        }
    return <msgs, types>;
    
}

@doc{Convert structured types, such as list<<int>>. Check here for certain syntactical 
conditions, such as: all field names must be distinct in a given type; lists require 
exactly one type argument; etc.}
public tuple[set[Message], AType] convertStructuredType(StructuredType st) {
    switch(st) {
        case (StructuredType) `list [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            if (size(l) == 1) {
                if (alabel(_,ltype) := l[0]) {
                    return < msgs + { warning("Field name ignored", st@\loc) }, makeListType(ltype) >;
                } else {
                    return < msgs, makeListType(l[0]) >;
                }            
            } else {
                return < msgs + { error("Non-well-formed type, type should have one type argument",st@\loc) }, alist(avoid()) >; 
            }
        }

        case (StructuredType) `set [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            if (size(l) == 1) {
                if (alabel(_,ltype) := l[0]) {
                    return < { warning("Field name ignored", st@\loc) }, makeSetType(ltype) >;
                } else {
                    return < msgs, makeSetType(l[0])>;
                }            
            } else {
                return < { error("Non-well-formed type, type should have one type argument",st@\loc) }, aset(avoid()) >  ; 
            }
        }

        case (StructuredType) `bag [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            if (size(l) == 1) {
                if (alabel(_,ltype) := l[0]) {
                    return < msgs + { warning("Field name ignored", st@\loc) }, abag(ltype) >;
                } else {
                    return abag(l[0]);
                }            
            } else {
                return < msgs + { error("Non-well-formed type, type should have one type argument",st@\loc) }, abag(avoid()) >; 
            }
        }

        case (StructuredType) `map [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            if (size(l) == 2) {
                if (alabel(dl,dt) := l[0] && alabel(rl,rt) := l[1] && dl != rl) {
                    return < msgs, amap(l[0],l[1]) >;
                } else if (alabel(dl,dt) := l[0] && alabel(rl,rt) := l[1] && dl == rl) {
                    return < msgs + { error("Non-well-formed type, labels must be distinct", st@\loc) }, amap(dt,rt) >;
                } else if (alabel(dl,dt) := l[0] && alabel(rl,rt) !:= l[1]) {
                    return < msgs + { warning("Field name ignored, field names must be provided for both fields or for none", st@\loc) }, amap(dt,l[1]) >;
                } else if (alabel(dl,dt) !:= l[0] && alabel(rl,rt) := l[1]) {
                    return <msgs + { warning("Field name ignored, field names must be provided for both fields or for none", st@\loc) }, amap(l[0],rt) >;
                } else {
                    return <msgs, amap(l[0],l[1]) >;
                }            
            } else {
                return <  msgs + { error("Non-well-formed type, type should have two type argument",st@\loc) }, amap(avoid(),avoid()) >; 
            }
        }

        case (StructuredType) `rel [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            labels = {fl | alabel(fl,_) <- l};
            labelsList = [fl | alabel(fl,_) <- l];
            if (size(l) == size(labels) || size(labels) == 0) {
                return <msgs, \rel(l)>;
            } else if (size(labels) > 0 && size(labels) != size(labelsList)) {
                return <msgs + { error("Non-well-formed type, labels must be distinct", st@\loc) }, \rel([ (alabel(fl,ft) := li) ? ft : li | li <- l ]) >;
            } else if (size(labels) > 0) {
                return <msgs + { warning("Field name ignored, field names must be provided for all fields or for none", st@\loc) }, \rel([ (alabel(fl,ft) := li) ? ft : li | li <- l ]) >;
            }
        }
        
        case (StructuredType) `lrel [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            labelsList = [fl | alabel(fl,_) <- l];
            labels = {*labelsList};
            if (size(l) == size(labels) || size(labels) == 0) {
                return < msgs, alrel(l)>;
            } else if (size(labels) > 0 && size(labels) != size(labelsList)) {
                return < msgs + { error("Non-well-formed type, labels must be distinct", st@\loc) }, alrel([ (alabel(fl,ft) := li) ? ft : li | li <- l ]) >;
            } else if (size(labels) > 0) {
                return < msgs + { warning("Field name ignored, field names must be provided for all fields or for none", st@\loc) }, alrel([ (alabel(fl,ft) := li) ? ft : li | li <- l ]) >;
            }
        }

        case (StructuredType) `tuple [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            labels = {fl | alabel(fl,_) <- l};
            labelsList = [fl | alabel(fl,_) <- l];
            if (size(l) == size(labels) || size(labels) == 0) {
                return < msgs, atuple(l) >;
            } else if (size(labels) > 0 && size(labels) != size(labelsList)) {
                return < msgs + { error("Non-well-formed type, labels must be distinct", st@\loc) }, atuple([ (alabel(fl,ft) := li) ? ft : li | li <- l ]) >;
            } else if (size(labels) > 0) {
                return < msgs + { warning("Field name ignored, field names must be provided for all fields or for none", st@\loc) }, atuple([ (alabel(fl,ft) := li) ? ft : li | li <- l ]) >;
            }
        }

        case (StructuredType) `type [ < {TypeArg ","}+ tas > ]` : {
            <msgs, l> = convertTypeArgList(tas);
            if (size(l) == 1) {
                if (alabel(_,ltype) := l[0]) {
                    return < msgs + { warning("Field name ignored", st@\loc) }, areified(ltype) >;
                } else {
                    return < msgs, areified(l[0]) >;
                }            
            } else {
                return < msgs + { error("Non-well-formed type, type should have one type argument",st@\loc) }, areified(avoid()) >; 
            }
        }

        case (StructuredType) `<BasicType bt> [ < {TypeArg ","}+ tas > ]` : {
                return < msgs + {error("Type <bt> does not accept type parameters",st@\loc)}, avoid() >;
        }
    }
}

@doc{Convert Rascal function types into their abstract representation.}
public tuple[set[Message], AType] convertFunctionType(FunctionType ft) {
    if ((FunctionType) `<Type t> ( <{TypeArg ","}* tas> )` := ft) {
        <msg, l> = convertTypeArgList(tas);
        <msgs1, tp> = convertType(t);
        msgs += msgs1;
        if (size(l) == 0) {
            return < msgs, afunc(tp, [], []) >;
        } else {
            labels = {fl | alabel(fl,_) <- l};
            labelsList = [fl | alabel(fl,_) <- l];
            if (size(l) == size(labels) || size(labels) == 0) {
                return < msgs, afunc(tp, l, []) >;
            } else if (size(labels) > 0 && size(labels) != size(labelsList)) {
                return < msgs + { error("Non-well-formed type, labels must be distinct", ft@\loc) }, afunc(tp, [ (alabel(fl,ftype) := li) ? ftype : li | li <- l ], []) >;
            } else if (size(labels) > 0) {
                return < msgs + { warning("Field name ignored, field names must be provided for all fields or for none", ft@\loc) }, afunc(tp, [ (alabel(fl,ftype) := li) ? ftype : li | li <- l ], []) >;
            }
        } 
    }
}

@doc{Convert Rascal user types into their abstract representation.}
public tuple[set[Message], AType] convertUserType(UserType ut) {
    switch(ut) {
        case (UserType) `<QualifiedName n>` : return <{}, \aadt("<n>",[], []) >;
        case (UserType) `<QualifiedName n>[ <{Type ","}+ ts> ]` : return \aadt(convertName(n),[convertType(ti) | ti <- ts]);
    }
}

//public Symbol convertSymbol(Sym sym) = sym2symbol(sym)[@at=sym@\loc];  

@doc{Get the raw Name component from a user type.}
public Name getUserTypeRawName(UserType ut) {
    switch(ut) {
        case (UserType) `<QualifiedName n>` : return getLastName(n);
        case (UserType) `<QualifiedName n>[ <{Type ","}+ ts> ]` : return getLastName(n);
    }
}

@doc{Convert Rascal type variables into their abstract representation.}
public tuple[set[Message], AType] convertTypeVar(TypeVar tv) {
    switch(tv) {
        case (TypeVar) `& <Name n>` : return <{}, aparameter(getSimpleName(convertName(n)),avalue())[@boundGiven=false] >;
        case (TypeVar) `& <Name n> \<: <Type tb>` : {
            <msgs, tp> = convertType(tb);
            return <msgs, aparameter(getSimpleName(convertName(n)),tp)[@boundGiven=true] >;
        }
    }
}

@doc{Convert Rascal data type selectors into an abstract representation.}
@todo{Implement once this is in use.}
public tuple[set[Message], AType] convertDataTypeSelector(DataTypeSelector dts) {
    switch(dts) {
        case (DataTypeSelector) `<QualifiedName n1> . <Name n2>` : throw "Not implemented";
    }
}

@doc{Main driver routine for converting Rascal types into abstract type representations.}
public tuple[set[Message], AType] convertType(Type t) {
    switch(t) {
        case (Type) `<BasicType bt>` : return convertBasicType(bt);
        case (Type) `<StructuredType st>` : return convertStructuredType(st);
        case (Type) `<FunctionType ft>` : return convertFunctionType(ft);
        case (Type) `<TypeVar tv>` : return convertTypeVar(tv);
        case (Type) `<UserType ut>` : return convertUserType(ut);
        case (Type) `<DataTypeSelector dts>` : return convertDataTypeSelector(dts);
        case (Type) `<Sym sym>` : return convertSymbol(sym);
        case (Type) `( <Type tp> )` : return convertType(tp);
        default : { throw "Error in convertType, unexpected type syntax: <t>"; }
    }
}

@doc{A parsing function, useful for generating test cases.}
public Type parseType(str s) {
    return parse(#Type, s);
}