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