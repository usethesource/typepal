@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
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