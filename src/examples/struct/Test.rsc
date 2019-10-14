module examples::struct::Test

import examples::struct::Syntax;

extend examples::struct::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel structTModelForTree(Tree pt){
    return collectAndSolve(pt, config = structConfig());
}

TModel structTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal/src/examples/struct/<mname>.struct|).top;
    return structTModelForTree(pt);
}

bool structTests() {
    return runTests([|project://typepal/src/examples/struct/tests.ttl|], 
                    #start[Program],
                    TModel (Tree t) { return structTModelForTree(t); },
                    runName = "Struct");
}

value main()
    = structTests();