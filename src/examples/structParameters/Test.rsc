module examples::structParameters::Test

import examples::structParameters::Syntax;

extend examples::structParameters::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structParametersTModelForTree(Tree pt){
    return collectAndSolve(pt, config = structParametersConfig());
}

TModel structParametersTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal/src/examples/structParameters/<mname>.struct|).top;
    return structParametersTModelForTree(pt);
}

bool structParametersTests() {
    return runTests([|project://typepal/src/examples/structParameters/tests.ttl|], 
                     #start[Program], 
                     TModel (Tree t) { return structParametersTModelForTree(t); },
                     runName = "StructParameters");
}

value main()
    = structParametersTests();