@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::fwjava::Test

import examples::fwjava::Syntax;
extend examples::fwjava::Checker;
extend analysis::typepal::TestFramework;

import ParseTree;

// ----  Examples & Tests --------------------------------

TModel fwjTModelForTree(Tree pt){
    if(pt has top) pt = pt.top;
    
    c = newCollector("fwj", pt, fwjConfig());
    fwjPreCollectInitialization(pt, c);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

TModel fwjTModelFromName(str mname, bool _){
    pt = parse(#start[FWJProgram], |project://typepal/src/examples/fwjava/<mname>.fwj|).top;
    return fwjTModelForTree(pt);
}

test bool fwjTests() {
    return runTests([|project://typepal/src/examples/fwjava/tests.ttl|], 
                     #start[FWJProgram], 
                     TModel (Tree t) { return fwjTModelForTree(t); },
                     runName = "FwJava");
}

test bool fwjUseDefTests1() = checkUseDefsOf("cpt");
test bool fwjUseDefTests2() = checkUseDefsOf("pair");
test bool fwjUseDefTests3() = checkUseDefsOf("tmp");

private bool checkUseDefsOf(str name) {
    tm = fwjTModelFromName(name, false);
    assert size(tm.useDef) > 0 : "Expected: \>0 use-defs. Actual: <size(tm.useDef)>.";

    for (<lUse, lDef> <- tm.useDef) {
        uses = [u | u: use(_, _, lUse, _, _) <- tm.uses];
        assert [] != uses : "Expected: Use at <lUse>. Actual: No use.";

        defs = [d | d: <_, _, _, _, lDef, _> <- tm.defines];
        assert [] != defs : "Expected: Def at <lDef>. Actual: No def."; 

        for (u <- uses, d <- defs) {
            assert u.id == d.id : "Expected: Equal `id`. Actual: `<u.id>` (use) vs. `<d.id>` (def)";
            assert u.orgId == d.orgId : "Expected: Equal `orgId`. Actual: `<u.id>` (use) vs. `<d.id>` (def)";
        }
    }

    return true;
}

value main() = fwjTests();