module examples::fixedMembers::Test

import examples::fixedMembers::Syntax;
extend examples::fixedMembers::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;


// ---- Testing ---------------------------------------------------------------

TModel fixedMembersTModelForTree(Tree pt, bool debug = false){
    return collectAndSolve(pt, config = fixedMembersConfig());
}

TModel fixedMembersTModelFromName(str mname, bool debug = false){
    pt = parse(#start[Program], |project://typepal/src/examples/fixedMembers/<mname>.alias|).top;
    return fixedMembersTModelForTree(pt, debug=debug);
}

bool fixedMembersTests(bool debug = false) {
    return runTests([|project://typepal/src/examples/fixedMembers/fixedMembers.ttl|], 
                    #start[Program], 
                    TModel (Tree t) { return fixedMembersTModelForTree(t, debug=debug); },
                    runName = "fixedMembers");
}

bool main() = fixedMembersTests();