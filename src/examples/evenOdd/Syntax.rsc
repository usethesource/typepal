module examples::evenOdd::Syntax

extend examples::CommonLex; 

start syntax EvenOdd
    = Statement+ statements
    ;
     
syntax Statement
    = "even" Integer integer ";"
    | "odd" Integer integer ";"
    ;

keyword Reserved = "even" | "odd";