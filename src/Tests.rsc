module Tests
extend Constraints;

data AType   
    = intType()                                     // int type
    | boolType()                                    // bool type
    | functionType(AType from, AType to)            // function type
    ;
    
test bool uni1() = <true, _> := unify(intType(), intType(), ());
test bool uni2() = <false, _> := unify(boolType(), intType(), ());

public AType tv1 = tvar(|typevar:///0000000001|);
public AType tv2 = tvar(|typevar:///0000000002|);

public AType gtv1 = tvar(|typevar:///0000000101|);
public AType gtv2 = tvar(|typevar:///0000000102|);

test bool uni3() = <true, _> := unify(tv1, intType(), ());

test bool uni4() = <true, _> := unify(tv2, boolType(), ());

test bool uni5() = <true, _> := unify(functionType(tv1, tv2), functionType(intType(), boolType()), ());

test bool uni6() = <true, _> := unify(tv1, gtv1, ());

test bool uni7() = <true, _> := unify(functionType(tv1, tv2), functionType(gtv1, gtv2), ());