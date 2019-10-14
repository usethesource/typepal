module examples::untypedFun::Test

import examples::untypedFun::Syntax;

extend examples::untypedFun::Checker;
extend analysis::typepal::TestFramework;

// ----  Examples & Tests --------------------------------

private Expression sample(str name) = parse(#start[Expression], |project://typepal/src/examples/untypedFun/<name>.ufun|).top;

list[Message] untypedFunCheck(str name){
    return untypedFunTModelForTree(sample(name)).messages;
}

TModel untypedFunTModelForTree(Tree pt)
    = collectAndSolve(pt);

bool untypedFunTests()
    = runTests([|project://typepal/src/examples/untypedFun/tests.ttl|], #Expression, untypedFunTModelForTree, runName="UntypedFun");

value main() = untypedFunTests();
