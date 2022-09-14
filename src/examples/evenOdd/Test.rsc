module examples::evenOdd::Test

//import ParseTree;
import examples::evenOdd::Syntax; 

extend examples::evenOdd::Checker;
extend analysis::typepal::TestFramework;    // TypePal test utilities
import ParseTree;                           // In order to parse tests

// ---- Testing ---------------------------------------------------------------

TModel evenOddTModelForTree(Tree pt){
    if(pt has top) pt = pt.top;
    c = newCollector("collectAndSolve", pt,  tconfig());    // TODO get more meaningfull name
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel evenOddTModelFromStr(str text){
    pt = parse(#start[EvenOdd], text).top;
    return evenOddTModelForTree(pt);
}

test bool evenOddTests() {
     return runTests([|home:///git/typepal/src/examples/evenOdd/tests.ttl|], 
                     #EvenOdd, 
                     evenOddTModelForTree, 
                     runName="EvenOdd");
}

value  main() {
    return evenOddTests();
}