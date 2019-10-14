module examples::ql::Test

import examples::ql::Syntax;
extend examples::ql::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel qlTModelForName(str name) {
    Tree pt = parse(#start[Form], |project://typepal/src/examples/ql/examples/<name>.ql|);
    return collectAndSolve(pt);
}

TModel qlTModelForTree(Tree pt) {
    return collectAndSolve(pt);
}

test bool qlTests() {
    return runTests([|project://typepal/src/examples/ql/tests.ttl|], #start[Form], 
                     TModel (Tree t) { return qlTModelForTree(t); },
                     runName = "QL");
}

value main()
    = qlTests();