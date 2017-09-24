module rascal::AType

//import Type;
import Node;
extend typepal::AType;
import rascal::ATypeUtils;
import lang::rascal::\syntax::Rascal;
import lang::rascal::types::AbstractType;
import lang::rascal::types::AbstractName;

alias Keyword = tuple[AType fieldType, str fieldName, Expression defaultExp];
alias Field   = tuple[AType fieldType, str fieldName];

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
     | afunc(AType ret, AType formals, list[Keyword] kwFormals)
     | aadt(str adtName, list[AType] parameters, list[Keyword] common)
     | acons(AType adt, str consName, list[Field] fields, list[Keyword] kwFields)
     | amodule(str mname)
     | aparameter(str pname, AType bound) 
     | alabel(str lname, AType atype)
     | aalias(str aname, list[AType] parameters, AType aliased)
     ;

AType overloadedAType(rel[Key, AType] overloads){
    if(all(<Key k, AType t> <- overloads, aadt(adtName, common) := t)){
      cm = [];
      RName adtName;
      for(<Key k, AType t> <- overloads, aadt(adtName1, common) := t){
        adtName = adtName1;
        cm += common;
      }
      //println("overloadedAType: overloads <overloads>
      //        '<cm>");
      return aadt(adtName, cm);
    }
    fail;
}

bool myIsSubType(AType t1, AType t2) = asubtype(t1, t2);
//{ res = asubtype(t1, t2); println("asubtype(<t1>, <t2>) ==\> <res>"); return res;}

//bool myIsSubType(AType t1, AType t2) {
//    //println("myIsSubType: <fmt(t1)>, <fmt(t2)>");
//    
//    if(aadt(adtName1, common1) := t1){
//        if(aadt(adtName2, common2) := t2){
//            return adtName1 == adtName2;
//        }
//        if(overloadedAType(rel[Key, AType] overloads2) := t2){
//            <k, tp> = getOneFrom(overloads2);
//            return aadt(adtName1, common) := tp;
//        }
//        return subtype(adt(adtName1, []), toSymbol(t2));
//    }
//    if(overloadedAType(rel[Key, AType] overloads1) := t1){
//        if(aadt(adtName2, common2) := t2){
//           <k, tp> = getOneFrom(overloads1);
//           return aadt(adtName2, common) := tp;
//        }
//       if(overloadedAType(rel[Key, AType] overloads2) := t2){
//          <k1, tp1> = getOneFrom(overloads1);
//          <k2, tp2> = getOneFrom(overloads2);
//          return aadt(adtName, common1) := tp1 && aadt(adtName, common2) := tp2;
//       } else {
//          return false;
//       }
//    }
//    
//    return subtype(toSymbol(t1), toSymbol(t2));
//}

AType myLUB(AType t1, AType t2) = lub(t1, t2); //toAType(lub(toSymbol(t1), toSymbol(t2)));

AType myATypeMin() = avoid();
AType myATypeMax() = avalue();

public set[AType] numericTypes = { aint(), areal(), arat(), anum() };

@doc{
.Synopsis
Subtype on types.
}       
bool subtype(type[&T] t, type[&U] u) = subtype(t.symbol, u.symbol);

@doc{
.Synopsis
This function documents and implements the subtype relation of Rascal's type system. 
}

bool asubtype(AType s, s) = true;
bool asubtype(AType s, AType t) = false;

bool asubtype(overloadedAType(overloads), AType r) = all(<k, tp> <- overloads, asubtype(tp, r));
bool asubtype(AType l, overloadedAType(overloads)) = all(<k, tp> <- overloads, asubtype(l, tp));

bool asubtype(AType _, avalue()) = true;

bool asubtype(avoid(), AType _) = true;

bool asubtype(acons(AType a, _, list[AType] _), a) = true;
bool asubtype(acons(AType a, str name, list[AType] ap), acons(a,name,list[AType] bp)) = asubtype(ap,bp);

bool asubtype(aadt(str _, list[AType] _, list[Keyword] _), anode()) = true;
bool asubtype(aadt(str n, list[AType] l, list[Keyword] _), aadt(n, list[AType] r, list[Keyword] _)) = asubtype(l, r);

bool asubtype(aalias(str _, list[AType] _, AType aliased), AType r) = asubtype(aliased, r);
bool asubtype(AType l, aalias(str _, list[AType] _, AType aliased)) = asubtype(l, aliased);

bool asubtype(aint(), anum()) = true;
bool asubtype(arat(), anum()) = true;
bool asubtype(areal(), anum()) = true;

bool asubtype(atuple(AType l), atuple(AType r)) = asubtype(l, r);

// list and lrel
bool asubtype(alist(AType s), alist(AType t)) = asubtype(s, t); 
bool asubtype(alrel(AType l), alrel(AType r)) = asubtype(l, r);

bool asubtype(alist(AType s), alrel(AType r)) = asubtype(s, atuple(r));
bool asubtype(alrel(AType l), alist(AType r)) = asubtype(atuple(l), r);

// set and rel
bool asubtype(aset(AType s), aset(AType t)) = asubtype(s, t);
bool asubtype(arel(AType l), arel(AType r)) = asubtype(l, r);

bool asubtype(aset(AType s), arel(AType r)) = asubtype(s, atuple(r));
bool asubtype(arel(AType l), aset(AType r)) = asubtype(atuple(l), r);

bool asubtype(abag(AType s), abag(AType t)) = asubtype(s, t);  

bool asubtype(amap(AType from1, AType to1), amap(AType from2, AType to2)) = asubtype(from1, from2) && asubtype(to1, to2);

bool asubtype(afunc(AType r1, AType p1, list[Keyword] _), AType f2) = asubtype(afunc(r1, p1), f2);
bool asubtype(AType f2, afunc(AType r1, AType p1, list[Keyword] _)) = asubtype(f2, afunc(r1, p1));
bool asubtype(afunc(AType r1, AType p1, list[Keyword] _), afunc(AType r2, AType p2, list[Keyword] _)) = asubtype(r1, r2) && asubtype(p2, p1); // note the contra-variance of the argument types

bool asubtype(aparameter(str _, AType bound), AType r) = asubtype(bound, r);
bool asubtype(AType l, aparameter(str _, AType bound)) = asubtype(l, bound);

bool asubtype(alabel(str _, AType s), AType t) = asubtype(s,t);
bool asubtype(AType s, alabel(str _, AType t)) = asubtype(s,t);

bool asubtype(areified(AType s), areified(AType t)) = asubtype(s,t);
bool asubtype(areified(AType s), anode()) = true;

bool asubtype(list[AType] l, list[AType] r) = all(i <- index(l), asubtype(l[i], r[i])) when size(l) == size(r) && size(l) > 0;
default bool asubtype(list[AType] l, list[AType] r) = size(l) == 0 && size(r) == 0;

@doc{
.Synopsis
Check if two types are comparable, i.e., have a common supertype.
}
bool comparable(AType s, AType t) = asubtype(s,t) || asubtype(t,s);

@doc{
.Synopsis
Check if two types are equivalent.
}
bool equivalent(AType s, AType t) = asubtype(s,t) && asubtype(t,s);


@doc{
.Synopsis
Structural equality between values. 

.Description
The difference is that no implicit coercions are done between values of incomparable types, such as == does for
int, real and rat.

.Examples

[source,rascal-shell]
----
import Type;
1 == 1.0
eq(1,1.0)
----
}
@javaClass{org.rascalmpl.library.Type}
public java bool eq(value x, value y);

int size(atypeList(list[AType] l)) = size(l);

@doc{
.Synopsis
The least-upperbound (lub) between two types.

.Description
This function documents and implements the lub operation in Rascal's type system. 
}
AType lub(AType s, s) = s;
default AType lub(AType s, AType t) = avalue();

AType lub(avalue(), AType t) = avalue();
AType lub(AType s, avalue()) = avalue();
AType lub(avoid(), AType t) = t;
AType lub(AType s, avoid()) = s;
AType lub(aint(), anum()) = anum();
AType lub(aint(), areal()) = anum();
AType lub(aint(), arat()) = anum();
AType lub(arat(), anum()) = anum();
AType lub(arat(), areal()) = anum();
AType lub(arat(), aint()) = anum();
AType lub(areal(), anum()) = anum();
AType lub(areal(), aint()) = anum();
AType lub(areal(), arat()) = anum();
AType lub(anum(), aint()) = anum();
AType lub(anum(), areal()) = anum();
AType lub(anum(), arat()) = anum();

AType lub(aset(AType s), aset(AType t)) = aset(lub(s, t));  
AType lub(aset(AType s), arel(AType ts)) = aset(lub(s,atuple(ts)));  
AType lub(arel(AType ts), aset(AType s)) = aset(lub(s,atuple(ts)));

AType lub(arel(AType l), arel(AType r)) = arel(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(l))) when size(l) == size(r) && allLabeled(l) && allLabeled(r) && getLabels(l) == getLabels(r);
AType lub(arel(AType l), arel(AType r)) = arel(lub(stripLabels(l), stripLabels(r))) when size(l) == size(r) && allLabeled(l) && allLabeled(r) && getLabels(l) != getLabels(r);
AType lub(arel(AType l), arel(AType r)) = arel(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(l))) when size(l) == size(r) && allLabeled(l) && noneLabeled(r);
AType lub(arel(AType l), arel(AType r)) = arel(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(r))) when size(l) == size(r) && noneLabeled(l) && allLabeled(r);
AType lub(arel(AType l), arel(AType r)) = arel(lub(stripLabels(l), stripLabels(r))) when size(l) == size(r) && !allLabeled(l) && !allLabeled(r);
AType lub(arel(AType l), arel(AType r)) = aset(avalue()) when size(l) != size(r);

AType lub(alist(AType s), alist(AType t)) = alist(lub(s, t));  
AType lub(alist(AType s), alrel(AType ts)) = alist(lub(s,atuple(ts)));  
AType lub(alrel(AType ts), alist(AType s)) = alist(lub(s,atuple(ts)));

AType lub(alrel(AType l), alrel(AType r)) = alrel(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(l))) when size(l) == size(r) && allLabeled(l) && allLabeled(r) && getLabels(l) == getLabels(r);
AType lub(alrel(AType l), alrel(AType r)) = alrel(lub(stripLabels(l), stripLabels(r))) when size(l) == size(r) && allLabeled(l) && allLabeled(r) && getLabels(l) != getLabels(r);
AType lub(alrel(AType l), alrel(AType r)) = alrel(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(l))) when size(l) == size(r) && allLabeled(l) && noneLabeled(r);
AType lub(alrel(AType l), alrel(AType r)) = alrel(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(r))) when size(l) == size(r) && noneLabeled(l) && allLabeled(r);
AType lub(alrel(AType l), alrel(AType r)) = alrel(lub(stripLabels(l), stripLabels(r))) when size(l) == size(r) && !allLabeled(l) && !allLabeled(r);
AType lub(alrel(AType l), alrel(AType r)) = alist(avalue()) when size(l) != size(r);

AType lub(atuple(AType l), atuple(AType r)) = atuple(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(l))) when size(l) == size(r) && allLabeled(l) && allLabeled(r) && getLabels(l) == getLabels(r);
AType lub(atuple(AType l), atuple(AType r)) = atuple(lub(stripLabels(l), stripLabels(r))) when size(l) == size(r) && allLabeled(l) && allLabeled(r) && getLabels(l) != getLabels(r);
AType lub(atuple(AType l), atuple(AType r)) = atuple(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(l))) when size(l) == size(r) && allLabeled(l) && noneLabeled(r);
AType lub(atuple(AType l), atuple(AType r)) = atuple(addLabels(lub(stripLabels(l), stripLabels(r)),getLabels(r))) when size(l) == size(r) && noneLabeled(l) && allLabeled(r);
AType lub(atuple(AType l), atuple(AType r)) = atuple(lub(stripLabels(l), stripLabels(r))) when size(l) == size(r) && ! ( (allLabeled(l) && allLabeled(r)) || (allLabeled(l) && noneLabeled(r)) || (noneLabeled(l) && allLabeled(r)));

AType lub(amap(alabel(str lfl, AType lf), alabel(str ltl, AType lt)), amap(alabel(str rfl, AType rf), alabel(str rtl, AType rt))) = amap(alabel(lfl, lub(lf,rf)), alabel(ltl, lub(lt,rt))) when lfl == rfl && ltl == rtl;
AType lub(amap(alabel(str lfl, AType lf), alabel(str ltl, AType lt)), amap(alabel(str rfl, AType rf), alabel(str rtl, AType rt))) = amap(lub(lf,rf), lub(lt,rt)) when lfl != rfl || ltl != rtl;
AType lub(amap(alabel(str lfl, AType lf), alabel(str ltl, AType lt)), amap(AType rf, AType rt)) = amap(alabel(lfl, lub(lf,rf)), alabel(ltl, lub(lt,rt))) when alabel(_,_) !:= rf && alabel(_,_) !:= rt;
AType lub(amap(AType lf, AType lt), amap(alabel(str rfl, AType rf), alabel(str rtl, AType rt))) = amap(alabel(rfl, lub(lf,rf)), alabel(rtl, lub(lt,rt))) when alabel(_,_) !:= lf && alabel(_,_) !:= lt;
AType lub(amap(AType lf, AType lt), amap(AType rf, AType rt)) = amap(lub(lf,rf), lub(lt,rt)) when alabel(_,_) !:= lf && alabel(_,_) !:= lt && alabel(_,_) !:= rf && alabel(_,_) !:= rt;

AType lub(abag(AType s), abag(AType t)) = abag(lub(s, t));
AType lub(aadt(str n, list[AType] _), anode()) = anode();
AType lub(anode(), aadt(str n, list[AType] _, list[Keyword] _)) = anode();
AType lub(aadt(str n, list[AType] lp, list[Keyword] _), aadt(n, list[AType] rp,list[Keyword] _)) = aadt(n, addParamLabels(lub(lp,rp),getParamLabels(lp)), []) when size(lp) == size(rp) && getParamLabels(lp) == getParamLabels(rp) && size(getParamLabels(lp)) > 0;
AType lub(aadt(str n, list[AType] lp, list[Keyword] _), aadt(n, list[AType] rp, list[Keyword] _)) = aadt(n, lub(lp,rp), []) when size(lp) == size(rp) && size(getParamLabels(lp)) == 0;
AType lub(aadt(str n, list[AType] lp, list[Keyword] _), aadt(str m, list[AType] rp, list[Keyword] _)) = anode() when n != m;
AType lub(aadt(str ln, list[AType] lp, list[Keyword] _), acons(AType b, _, list[AType] _)) = lub(aadt(ln,lp,[]),b);

AType lub(acons(AType la, _, list[AType] _), acons(AType ra, _, list[AType] _)) = lub(la,ra);
AType lub(acons(AType a, _, list[AType] lp), aadt(str n, list[AType] rp)) = lub(a,aadt(n,rp));
AType lub(acons(AType _, _, list[AType] _), anode()) = anode();

AType lub(aalias(str _, list[AType] _, AType aliased), AType r) = lub(aliased, r);
AType lub(AType l, aalias(str _, list[AType] _, AType aliased)) = lub(l, aliased);

bool keepParams(aparameter(str s1, AType bound1), aparameter(str s2, AType bound2)) = s1 == s2 && equivalent(bound1,bound2);

AType lub(AType l:aparameter(str s1, AType bound1), AType r:aparameter(str s2, AType bound2)) = l when keepParams(l,r);
AType lub(AType l:aparameter(str s1, AType bound1), AType r:aparameter(str s2, AType bound2)) = lub(bound1,bound2) when !keepParams(l,r);
AType lub(aparameter(str _, AType bound), AType r) = lub(bound, r) when !(isTypeVar(r));
AType lub(AType l, aparameter(str _, AType bound)) = lub(l, bound) when !(isTypeVar(l));

AType lub(areified(AType l), areified(AType r)) = areified(lub(l,r));
AType lub(areified(AType l), anode()) = anode();

AType lub(afunc(AType lr, list[AType] lp, list[AType] lkw), afunc(AType rr, list[AType] rp, list[AType] rkw)) {
    lubReturn = lub(lr,rr);
    lubParams = glb(atuple(lp),atuple(rp));
    if (isTupleType(lubParams))
        return afunc(lubReturn, lubParams.ATypes, lkw == rkw ? lkw : []);
    else
        return avalue();
}

AType lub(alabel(_,AType l), AType r) = lub(l,r);
AType lub(AType l, alabel(_,AType r)) = lub(l,r);

public list[AType] lub(list[AType] l, list[AType] r) = [lub(l[idx],r[idx]) | idx <- index(l)] when size(l) == size(r); 
default list[AType] lub(list[AType] l, list[AType] r) = [avalue()]; 

private bool allLabeled(list[AType] l) = all(li <- l, alabel(_,_) := li);
private bool noneLabeled(list[AType] l) = all(li <- l, alabel(_,_) !:= li);
private list[str] getLabels(list[AType] l) = [ s | li <- l, alabel(s,_) := li ];
private list[AType] addLabels(list[AType] l, list[str] s) = [ alabel(s[idx],l[idx]) | idx <- index(l) ] when size(l) == size(s);
private default list[AType] addLabels(list[AType] l, list[str] s) { throw "Length of AType list <l> and label list <s> much match"; }
private list[AType] stripLabels(list[AType] l) = [ (alabel(_,v) := li) ? v : li | li <- l ]; 

private list[str] getParamLabels(list[AType] l) = [ s | li <- l, aparameter(s,_) := li ];
private list[AType] addParamLabels(list[AType] l, list[str] s) = [ aparameter(s[idx],l[idx]) | idx <- index(l) ] when size(l) == size(s);
private default list[AType] addParamLabels(list[AType] l, list[str] s) { throw "Length of AType list and label list much match"; } 


@doc{
.Synopsis
Determine if the given type is an int.
}
bool isIntType(aalias(_,_,AType at)) = isIntType(at);
bool isIntType(aparameter(_,AType tvb)) = isIntType(tvb);
bool isIntType(alabel(_,AType lt)) = isIntType(lt);
bool isIntType(aint()) = true;
default bool isIntType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a bool.
}
bool isBoolType(aalias(_,_,AType at)) = isBoolType(at);
bool isBoolType(aparameter(_,AType tvb)) = isBoolType(tvb);
bool isBoolType(alabel(_,AType lt)) = isBoolType(lt);
bool isBoolType(abool()) = true;
default bool isBoolType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a real.
}
bool isRealType(aalias(_,_,AType at)) = isRealType(at);
bool isRealType(aparameter(_,AType tvb)) = isRealType(tvb);
bool isRealType(alabel(_,AType lt)) = isRealType(lt);
bool isRealType(areal()) = true;
default bool isRealType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a rational.
}
bool isRatType(aalias(_,_,AType at)) = isRatType(at);
bool isRatType(aparameter(_,AType tvb)) = isRatType(tvb);
bool isRatType(alabel(_,AType lt)) = isRatType(lt);
bool isRatType(arat()) = true;
default bool isRatType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a string.
}
bool isStrType(aalias(_,_,AType at)) = isStrType(at);
bool isStrType(aparameter(_,AType tvb)) = isStrType(tvb);
bool isStrType(alabel(_,AType lt)) = isStrType(lt);
bool isStrType(astr()) = true;
default bool isStrType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a num.
}
bool isNumType(aalias(_,_,AType at)) = isNumType(at);
bool isNumType(aparameter(_,AType tvb)) = isNumType(tvb);
bool isNumType(alabel(_,AType lt)) = isNumType(lt);
bool isNumType(anum()) = true;
default bool isNumType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a node.
}
bool isNodeType(aalias(_,_,AType at)) = isNodeType(at);
bool isNodeType(aparameter(_,AType tvb)) = isNodeType(tvb);
bool isNodeType(alabel(_,AType lt)) = isNodeType(lt);
bool isNodeType(anode()) = true;
bool isNodeType(aadt(_,_)) = true;
default bool isNodeType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a void.
}
bool isVoidType(aalias(_,_,AType at)) = isVoidType(at);
bool isVoidType(aparameter(_,AType tvb)) = isVoidType(tvb);
bool isVoidType(alabel(_,AType lt)) = isVoidType(lt);
bool isVoidType(avoid()) = true;
default bool isVoidType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a value.
}
bool isValueType(aalias(_,_,AType at)) = isValueType(at);
bool isValueType(aparameter(_,AType tvb)) = isValueType(tvb);
bool isValueType(alabel(_,AType lt)) = isValueType(lt);
bool isValueType(avalue()) = true;
default bool isValueType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a loc.
}
bool isLocType(aalias(_,_,AType at)) = isLocType(at);
bool isLocType(aparameter(_,AType tvb)) = isLocType(tvb);
bool isLocType(alabel(_,AType lt)) = isLocType(lt);
bool isLocType(aloc()) = true;
default bool isLocType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a `datetime`.
}
bool isDateTimeType(aalias(_,_,AType at)) = isDateTimeType(at);
bool isDateTimeType(aparameter(_,AType tvb)) = isDateTimeType(tvb);
bool isDateTimeType(alabel(_,AType lt)) = isDateTimeType(lt);
bool isDateTimeType(\datetime()) = true;
default bool isDateTimeType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a set.
}
bool isSetType(aalias(_,_,AType at)) = isSetType(at);
bool isSetType(aparameter(_,AType tvb)) = isSetType(tvb);
bool isSetType(alabel(_,AType lt)) = isSetType(lt);
bool isSetType(aset(_)) = true;
bool isSetType(arel(_)) = true;
default bool isSetType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a relation.
}
bool isRelType(aalias(_,_,AType at)) = isRelType(at);
bool isRelType(aparameter(_,AType tvb)) = isRelType(tvb);
bool isRelType(alabel(_,AType lt)) = isRelType(lt);
bool isRelType(arel(_)) = true;
bool isRelType(aset(AType tp)) = true when isTupleType(tp);
default bool isRelType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a list relation.
}
bool isListRelType(aalias(_,_,AType at)) = isListRelType(at);
bool isListRelType(aparameter(_,AType tvb)) = isListRelType(tvb);
bool isListRelType(alabel(_,AType lt)) = isListRelType(lt);
bool isListRelType(alrel(_)) = true;
bool isListRelType(alist(AType tp)) = true when isTupleType(tp);
default bool isListRelType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a tuple.
}
bool isTupleType(aalias(_,_,AType at)) = isTupleType(at);
bool isTupleType(aparameter(_,AType tvb)) = isTupleType(tvb);
bool isTupleType(alabel(_,AType lt)) = isTupleType(lt);
bool isTupleType(atuple(_)) = true;
default bool isTupleType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a list.
}
bool isListType(aalias(_,_,AType at)) = isListType(at);
bool isListType(aparameter(_,AType tvb)) = isListType(tvb);
bool isListType(alabel(_,AType lt)) = isListType(lt);
bool isListType(alist(_)) = true;
bool isListType(alrel(_)) = true;
default bool isListType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a list relation.
}
bool isListRelType(aalias(_,_,AType at)) = isListRelType(at);
bool isListRelType(aparameter(_,AType tvb)) = isListRelType(tvb);
bool isListRelType(alabel(_,AType lt)) = isListRelType(lt);
bool isListRelType(alrel(_)) = true;
default bool isListRelType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a map.
}
bool isMapType(aalias(_,_,AType at)) = isMapType(at);
bool isMapType(aparameter(_,AType tvb)) = isMapType(tvb);
bool isMapType(alabel(_,AType lt)) = isMapType(lt);
bool isMapType(amap(_,_)) = true;
default bool isMapType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a bag (bags are not yet implemented).
}
bool isBagType(aalias(_,_,AType at)) = isBagType(at);
bool isBagType(aparameter(_,AType tvb)) = isBagType(tvb);
bool isBagType(alabel(_,AType lt)) = isBagType(lt);
bool isBagType(abag(_)) = true;
default bool isBagType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is an Abstract Data Type (ADT).
}
bool isADTType(aalias(_,_,AType at)) = isADTType(at);
bool isADTType(aparameter(_,AType tvb)) = isADTType(tvb);
bool isADTType(alabel(_,AType lt)) = isADTType(lt);
bool isADTType(aadt(_,_)) = true;
bool isADTType(areified(_)) = true;
default bool isADTType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a constructor.
}
bool isConstructorType(aalias(_,_,AType at)) = isConstructorType(at);
bool isConstructorType(aparameter(_,AType tvb)) = isConstructorType(tvb);
bool isConstructorType(alabel(_,AType lt)) = isConstructorType(lt);
bool isConstructorType(acons(AType _,str _,list[AType] _)) = true;
default bool isConstructorType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is an alias.
}
bool isAliasType(aalias(_,_,_)) = true;
bool isAliasType(aparameter(_,AType tvb)) = isAliasType(tvb);
bool isAliasType(alabel(_,AType lt)) = isAliasType(lt);
default bool isAliasType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a function.
}
bool isFunctionType(aalias(_,_,AType at)) = isFunctionType(at);
bool isFunctionType(aparameter(_,AType tvb)) = isFunctionType(tvb);
bool isFunctionType(alabel(_,AType lt)) = isFunctionType(lt);
bool isFunctionType(afunc(_,_,_)) = true;
bool isFunctionType(afunc(_,_)) = true;
//bool isFunctionType(\var-func(_,_,_)) = true;
default bool isFunctionType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is a reified type.
}
bool isReifiedType(aalias(_,_,AType at)) = isReifiedType(at);
bool isReifiedType(aparameter(_,AType tvb)) = isReifiedType(tvb);
bool isReifiedType(alabel(_,AType lt)) = isReifiedType(lt);
bool isReifiedType(areified(_)) = true;
default bool isReifiedType(AType _) = false;

@doc{
.Synopsis
Determine if the given type is an type variable (parameter).
}
bool isTypeVar(aparameter(_,_)) = true;
bool isTypeVar(aalias(_,_,AType at)) = isTypeVar(at);
bool isTypeVar(alabel(_,AType lt)) = isTypeVar(lt);
default bool isTypeVar(AType _) = false;

