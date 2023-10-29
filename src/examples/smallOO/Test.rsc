module examples::smallOO::Test

import examples::smallOO::Syntax;
extend examples::smallOO::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ---- Testing ---------------------------------------------------------------
               
TModel smallOOTModelForTree(Tree pt){
    return collectAndSolve(pt, config=smallConfig(), modelName="smalloo");
}

TModel smallOOTModelFromName(str mname){
    pt = parse(#start[Module], |project://typepal/src/examples/smallOO/<mname>.small|).top;
    return smallOOTModelForTree(pt);
}

list[Message] checkSmallOO(str mname) {
    return smallOOTModelFromName(mname).messages;
}

test bool smallOOTests() {
    return runTests([|project://typepal/src/examples/smallOO/tests.ttl|], 
                    #start[Module], 
                    TModel (Tree t) { return smallOOTModelForTree(t); },
                    runName = "SmallOO");
}

value main()
    = smallOOTests();