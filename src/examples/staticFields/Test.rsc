module examples::staticFields::Test

import examples::staticFields::Syntax;

extend examples::staticFields::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel staticFieldsTModelForTree(Tree pt){
    return collectAndSolve(pt, config=staticFieldsConfig());
}

TModel staticFieldsTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal/src/examples/staticFields/<mname>.struct|).top;
    return staticFieldsTModelForTree(pt);
}

bool staticFieldsTests() {
    return runTests([|project://typepal/src/examples/staticFields/tests.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return staticFieldsTModelForTree(t); },
                    runName = "StaticFields");
}

value main()
    = staticFieldsTests();