module examples::modfun::Test

import examples::modfun::Syntax;
extend examples::modfun::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Testing --------------------------------------------------------------

private ModFun modfunSample(str name) = parse(#ModFun, |project://typepal/src/examples/modfun/<name>.mfun|);

TModel modfunTModel(str name){
   return modfunTModelForTree(modfunSample(name));
}

TModel modfunTModelForTree(Tree pt){
    return collectAndSolve(pt);
}

TModel modfunTModelFromStr(str text){
    pt = parse(#start[ModFun], text).top;
    return modfunTModelForTree(pt);
}

list[Message] modfunCheck(str name) {
    tm = modfunTModel(name);
    return tm.messages;
}

bool modfunTests()
    = runTests([|project://typepal/src/examples/modfun/tests.ttl|], 
               #ModFun,
               modfunTModelForTree,
               runName = "ModFun");

value main() 
    =  modfunTests();