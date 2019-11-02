module examples::fwjava::Test

import examples::fwjava::Syntax;
extend examples::fwjava::Checker;
extend analysis::typepal::TestFramework;
import IO;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel fwjTModelForTree(Tree pt){
    if(pt has top) pt = pt.top;
    
    c = newCollector("FWJ checker", pt, config=fwjConfig());
    fwjPreCollectInitialization(pt, c);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel fwjTModelFromName(str mname, bool debug){
    pt = parse(#start[FWJProgram], |project://typepal/src/examples/fwjava/<mname>.fwj|).top;
    return fwjTModelForTree(pt);
}

test bool fwjTests() {
    return runTests([|project://typepal/src/examples/fwjava/tests.ttl|], 
                     #start[FWJProgram], 
                     TModel (Tree t) { return fwjTModelForTree(t); },
                     runName = "FwJava");
}

value main() = fwjTests();