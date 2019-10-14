module examples::calc::Test

import examples::calc::Syntax; 

extend examples::calc::Checker;
extend analysis::typepal::TestFramework;    // TypePal test utilities
import ParseTree;                           // In order to parse tests

// ---- Testing ---------------------------------------------------------------

TModel calcTModelForTree(Tree pt){
    return collectAndSolve(pt);
}

TModel calcTModelFromStr(str text){
    pt = parse(#start[Calc], text).top;
    return calcTModelForTree(pt);
}

bool calcTests() {
     return runTests([|project://typepal/src/examples/calc/tests.ttl|], 
                     #Calc, 
                     calcTModelForTree, 
                     runName="Calc");
}

bool main() = calcTests();