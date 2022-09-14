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