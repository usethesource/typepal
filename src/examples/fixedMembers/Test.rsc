module examples::fixedMembers::Test

import examples::fixedMembers::Syntax;
extend examples::fixedMembers::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;


// ---- Testing ---------------------------------------------------------------

TModel fixedMembersTModelForTree(Tree pt){
    return collectAndSolve(pt, config = fixedMembersConfig(), modelName="fixed-members");
}

TModel fixedMembersTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal/src/examples/fixedMembers/<mname>.alias|).top;
    return fixedMembersTModelForTree(pt);
}

test bool fixedMembersTests() {
    return runTests([|project://typepal/src/examples/fixedMembers/fixedMembers.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return fixedMembersTModelForTree(t); },
                    runName = "fixedMembers");
}

bool main() = fixedMembersTests();