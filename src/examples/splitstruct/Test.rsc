module examples::splitstruct::Test

import examples::splitstruct::Syntax;

extend examples::splitstruct::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel splitstructTModelForTree(Tree pt){
    return collectAndSolve(pt, config = splitstructConfig());
}

TModel splitstructTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal/src/examples/splitstruct/<mname>.struct|).top;
    return splitstructTModelForTree(pt);
}

test bool splitstructTests() {
    return runTests([|project://typepal/src/examples/splitstruct/tests.ttl|], 
                    #start[Program],
                    TModel (Tree t) { return splitstructTModelForTree(t); },
                    runName = "SplitStruct");
}

value main()
    = splitstructTests();