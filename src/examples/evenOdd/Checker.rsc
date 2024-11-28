@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::evenOdd::Checker

import String;

import examples::evenOdd::Syntax;            // The EvenOdd syntax
extend analysis::typepal::TypePal;          // TypePal

// ---- collect constraints for Even ------------------------------------------

bool isEven(Integer integer)
    = toInt("<integer>") mod 2 == 0;

void collect(current: (EvenOdd) `<Statement+ statements>`, Collector c){
     collect(statements, c);
}

void collect(current: (Statement) `even <Integer integer>;`, Collector c){
    c.require("even", current, [], 
        void(Solver s) { s.requireTrue(isEven(integer), error(current, "Even statement should contain an even number, found %q", integer));
    });
}

void collect(current: (Statement) `odd <Integer integer>;`, Collector c){
    c.require("odd", current, [], 
        void(Solver s) { s.requireTrue(!isEven(integer), error(current, "Odd statement should contain an odd number, found %q", integer));
    });
}