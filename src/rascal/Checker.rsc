@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module rascal::Checker

import IO;
import String;
import util::Benchmark;

import lang::rascal::\syntax::Rascal;

extend typepal::TypePal;
extend typepal::TestFramework;

extend rascal::Declaration;
extend rascal::Expression;
extend rascal::Statement;
extend rascal::Pattern;

extend rascal::AType;
extend rascal::ATypeUtils;

start syntax Modules
    = Module+ modules;

// ----  Examples & Tests --------------------------------

private start[Expression] sampleExpression(str name) = parse(#start[Expression], |home:///git/TypePal/src/rascal/<name>.rsc-exp|);
private start[Module] sampleModule(str name) = parse(#start[Module], |home:///git/TypePal/src/rascal/<name>.rsc|);
private start[Modules] sampleModules(str name) = parse(#start[Modules], |home:///git/TypePal/src/rascal/<name>.mrsc|);

set[Message] validateModule(str name) {
    startTime = cpuTime();
    b = sampleModule(name).top;
    afterParseTime = cpuTime();
    m = extractFRModel(b, lookupFun=lookupWide);
    afterExtractTime = cpuTime();
    msgs = validate(m, lookupFun=lookupWide, debug=true).messages;
    afterValidateTime = cpuTime();
    //println("parse:    <(afterParseTime - startTime)/1000000> ms
    //        'extract:  <(afterExtractTime - afterParseTime)/1000000> ms
    //        'validate: <(afterValidateTime - afterExtractTime)/1000000> ms
    //        'total:    <(afterValidateTime - startTime)/1000000> ms");
    return msgs;
}

set[Message] validateModules(str name) {
    startTime = cpuTime();
    b = sampleModules(name).top;
    afterParseTime = cpuTime();
    m = extractFRModel(b, lookupFun=lookupWide);
    afterExtractTime = cpuTime();
    m = validate(m, lookupFun=lookupWide, debug=true);
    //iprintln(m);
    msgs = m.messages;
    afterValidateTime = cpuTime();
    //println("parse:    <(afterParseTime - startTime)/1000000> ms
    //        'extract:  <(afterExtractTime - afterParseTime)/1000000> ms
    //        'validate: <(afterValidateTime - afterExtractTime)/1000000> ms
    //        'total:    <(afterValidateTime - startTime)/1000000> ms");
    return msgs;
}

void testExp() {
    runTests(|project://TypePal/src/rascal/tests/exp.ttl|, #Expression, lookupFun=lookupWide);
}

void testPat() {
    runTests(|project://TypePal/src/rascal/tests/pat.ttl|, #Expression, lookupFun=lookupWide);
}

void testModules(str name) {
    runTests(|project://TypePal/src/rascal/tests/<name>.ttl|, #Modules, lookupFun=lookupWide);
}