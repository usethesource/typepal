module examples::pico::Test

import examples::pico::Syntax;
extend examples::pico::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel picoTModelFromName(str name) {
    Tree pt = parse(#start[Program], |project://typepal/src/examples/pico/<name>.pico|);
    return collectAndSolve(pt);
}

TModel picoTModelForTree(Tree pt) {
    return collectAndSolve(pt);
}

test bool picoTests() {
    return runTests([|project://typepal/src/examples/pico/tests.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return picoTModelForTree(t); },
                    runName = "Pico");
}

value main()
    = picoTests();