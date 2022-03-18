module examples::picoci::Test

import examples::picoci::Syntax;
extend examples::picoci::Checker;
extend analysis::typepal::TestFramework;
import String;

import ParseTree;

// ----  Examples & Tests --------------------------------

//TypePalConfig configci = tconfig(normalizeName  = toLowerCase);
//
//TModel picociTModelFromName(str name) {
//    Tree pt = parse(#start[Program], |project://typepal/src/examples/picoci/<name>.pico|);
//    return collectAndSolve(pt, config=configci);
//}
//
//TModel picociTModelForTree(Tree pt) {
//    return collectAndSolve(pt, config=configci);
//}
//
//test bool picociTests() {
//    return runTests([|project://typepal/src/examples/picoci/tests.ttl|], 
//                    #start[Program], 
//                    TModel (Tree t) { return picociTModelForTree(t); },
//                    runName = "PicoCI");
//}
//
//value main()
//    = picociTests();