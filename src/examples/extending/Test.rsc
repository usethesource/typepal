module examples::extending::Test

import examples::extending::Syntax;
extend examples::extending::Checker;

extend analysis::typepal::TestFramework;

import ParseTree;


// ---- Testing ---------------------------------------------------------------

TModel extendingTModelForTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config = extendingConfig());
}

TModel extendingTModelFromName(str mname, bool debug = false){
    pt = parse(#start[Program], |project://typepal/src/examples/extending/<mname>.xt|).top;
    return extendingTModelForTree(pt, debug=debug);
}

bool extendingTests(bool debug = false) {
    return runTests([|project://typepal/src/examples/extending/extending.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return extendingTModelForTree(t, debug=debug); },
                    runName = "extending");
}

bool main() = extendingTests();