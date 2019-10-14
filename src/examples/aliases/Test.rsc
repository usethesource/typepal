module examples::aliases::Test

import examples::aliases::Syntax;
extend  examples::aliases::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------

TModel aliasesTModelForTree(Tree pt){
    return collectAndSolve(pt, config = aliasesConfig());
}

TModel aliasesTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal/src/examples/aliases/<mname>.alias|).top;
    return aliasesTModelForTree(pt);
}

test bool aliasesTests() {
    return runTests([|project://typepal/src/examples/aliases/aliases.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return aliasesTModelForTree(t); },
                    runName = "Aliases");
}

bool main() = aliasesTests();