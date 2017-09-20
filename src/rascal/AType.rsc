module rascal::AType

import Type;
import Node;
import typepal::AType;
import lang::rascal::\syntax::Rascal;
import lang::rascal::types::AbstractType;
import lang::rascal::types::AbstractName;

data AType 
    =  aint()
     | abool()
     | areal()
     | arat()
     | astr()
     | anum()
     | anode()
     | avoid()
     | avalue()
     | aloc()
     | adatetime()
     | alist(AType elmType)
     | aset(AType elmType)
     | atuple(AType elemType)
     | amap(AType keyType, AType valType)
     | arel(AType elemType)
     | alrel(AType elemType)
     | afunc(AType ret, list[AType] formals, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals)
     | aadt(str adtName)
     | acons(str adtName, str consName, 
             lrel[AType fieldType, str fieldName] fields, 
             lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields)
     | amodule(str mname)
     ;

bool isSubType(AType t1, AType t2) = subtype(toSymbol(t1), toSymbol(t2));
AType getLUB(AType t1, AType t2) = toAType(lub(toSymbol(t1), toSymbol(t2)));

AType getVoid() = avoid();
AType getValue() = avalue();

public set[AType] numericTypes = { aint(), areal(), arat(), anum() };

Symbol toSymbol(aint()) = \int();
Symbol toSymbol(abool()) = \bool();
Symbol toSymbol(areal()) = \real();
Symbol toSymbol(arat()) = \rat();
Symbol toSymbol(astr()) = \str();
Symbol toSymbol(anum()) = \num();
Symbol toSymbol(anode()) = \node();
Symbol toSymbol(avoid()) = \void();
Symbol toSymbol(avalue()) = \value();
Symbol toSymbol(aloc()) = \loc();
Symbol toSymbol(adatetime()) = \datetime();
Symbol toSymbol(alist(AType elmType)) = \list(toSymbol(elmType));
Symbol toSymbol(aset(AType elmType)) = \set(toSymbol(elmType));
Symbol toSymbol(atuple(atypeList(list[AType] elmTypes))) = \tuple([toSymbol(elmType) | elmType <- elmTypes]);
Symbol toSymbol(amap(Atype t1, AType t2)) = \map(toSymbol(t1), toSymbol(t2));
Symbol toSymbol(arel(atypeList(list[AType] elmTypes))) = \rel([toSymbol(elmType) | elmType <- elmTypes]);
Symbol toSymbol(alrel(atypeList(list[AType] elmTypes))) = \lrel([toSymbol(elmType) | elmType <- elmTypes]);
Symbol toSymbol(aadt(str adtName)) = \adt(adtName, []);
Symbol toSymbol(tvar(name)) {
    throw TypeUnavailable();
}
default Symbol toSymbol(AType t) {
    throw "toSymbol cannot convert <t>";
}

AType toAType(\int()) = aint();
AType toAType(\bool()) = abool();
AType toAType(\real()) = areal();
AType toAType(\rat()) = arat();
AType toAType(\str()) = astr();
AType toAType(\num()) = anum();
AType toAType(\node()) = anode();
AType toAType(\void()) = avoid();
AType toAType(\value()) = avalue();
AType toAType(\loc()) = aloc();
AType toAType(\datetime()) = adatetime();
AType toAType(\list(Symbol elmType)) = alist(toAType(elmType));
AType toAType(\set(Symbol elmType)) = aset(toAType(elmType));
AType toAType(\tuple(list[Symbol] elmTypes)) = atuple(atypeList([toAType(elmType) | elmType <- elmTypes]));
AType toAType(\map(Symbol from, Symbol to)) = amap(toAType(from), toAType(to));
AType toAType(\rel(list[Symbol] elmTypes)) = arel(atypeList([toAType(elmType) | elmType <- elmTypes]));
AType toAType(\lrel(list[Symbol] elmTypes)) = alrel(atypeList([toAType(elmType) | elmType <- elmTypes]));
AType toAType(\adt(str adtName, list[Symbol] parameters)) = aadt(adtName);
AType toAType(\user(RSimpleName(str adtName))) = aadt(adtName);

default AType toAType(Symbol s){
    if(getName(s) == "user"){   // This is a hack since the "at" annotations on user prevent correct match
        if(RName rn := getChildren(s)[0]){
           return aadt(rn.name);
        }
    }
    throw "toAType: cannot convert <s>";
}

str AType2String(acons(str adtName, str consName, 
                 lrel[AType fieldType, str fieldName] fields, 
                 lrel[AType fieldType, str fieldName, Expression defaultExp] kwFields))
                 = "<adtName>:<consName>(<intercalate(",", ["<AType2String(ft)> <fn>" | <ft, fn> <- fields])>,<intercalate(",", ["<AType2String(ft)> <fn>=..." | <ft, fn, de> <- kwFields])>)";

str AType2String(afunc(AType ret, list[AType] formals, lrel[AType fieldType, str fieldName, Expression defaultExp] kwFormals))
                = "<AType2String(ret)>(<intercalate(",", [AType2String(f) | f <- formals])>,<intercalate(",", ["<AType2String(ft)> <fn>=..." | <ft, fn, de> <- kwFormals])>)";
                
str AType2String(AType t) = prettyPrintType(toSymbol(t));

