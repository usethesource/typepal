module examples::fun::Test

import examples::fun::Syntax;
extend examples::fun::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Testing --------------------------------------------------------------

private Fun funSample(str name) = parse(#Fun, |project://typepal/src/examples/fun/<name>.fun|);

TModel funTModel(str name){
   return funTModelForTree(funSample(name));
}

TModel funTModelForTree(Tree pt){
    return collectAndSolve(pt);
}

TModel funTModelFromStr(str text){
    pt = parse(#start[Fun], text).top;
    return funTModelForTree(pt);
}

list[Message] funCheck(str name) {
    tm = funTModel(name);
    return tm.messages;
}

test bool funTests() 
    =  runTests([|project://typepal/src/examples/fun/tests.ttl|], #Fun, funTModelForTree, runName="Fun");

value main() = funTests();
