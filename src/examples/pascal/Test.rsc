
@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::pascal::Test

import examples::pascal::Syntax;
extend examples::pascal::Checker;
extend analysis::typepal::TestFramework;
import ParseTree;
import IO;
import util::Reflective;

// ----  Examples & Tests --------------------------------


TModel pascalTModelForTree(Tree pt, str programName, PathConfig _, bool _){
    if(pt has top) pt = pt.top;
    
    c = newCollector(programName, pt, pascalConfig());
    pascalPreCollectInitialization(pt, c);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel pascalTModelForTree(Tree pt, bool _){
    if(pt has top) pt = pt.top;
    
    c = newCollector("pascal", pt, pascalConfig());
    pascalPreCollectInitialization(pt, c);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel pascalTModelForName(str mname, bool debug){
    pt = parse(#start[Program], |project://typepal/src/examples/pascal/examples/<mname>.pascal|).top;
    return pascalTModelForTree(pt, debug);
}

list[str] examples = ["beginend", "bisect", "complex", "convert", "cosine", "egfor", "egrepeat", "egwhile", "exponentiation", "exponentiation2",
                      "fcount", "graph1", "graph2", "inflation", "insert", "matrixmul", "minmax", "minmax2", "minmax2", 
                      "parameters", "person", "primes", 
                      "recursivegcd", "roman", "setop", "sideeffect", "summing", "traversal", "with"];

test bool pascalTests() {

    //println("**** PASCALTESTS DISABLED ****");
    //return true;
    bool ok = runTests([|project://typepal/src/examples/pascal/expression-tests.ttl|,
                        |project://typepal/src/examples/pascal/statement-tests.ttl|
                       ], #start[Program], TModel (Tree t) { return pascalTModelForTree(t, false); },
                       runName = "Pascal");
    println("Executing Pascal examples\r");
    int n = 0;
    for(ex <- examples){
        n += 1;
        msgs = pascalTModelForName(ex, false).messages;
        if(isEmpty(msgs)){
            print("<spinChar(n)> <ex>: ok\r");
        } else {
            println("<ex>:");
            println(msgs);
            ok = false;
        }
    }
    println("Executing Pascal examples: <ok>");
    return ok;
}

value main() 
    = pascalTests();