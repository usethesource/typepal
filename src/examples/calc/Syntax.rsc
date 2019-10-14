module examples::calc::Syntax

extend examples::CommonLex;     //<1>

start syntax Calc
    = Decl+                 //<2>
    ;

syntax Decl
    = "var" Id "=" Exp ";"  //<3>
    ;
   
syntax Exp 
   = Id                             //<4>
   | Integer                        //<5>
   | Boolean                        //<6>
   | bracket "(" Exp ")"            //<7>
   > left Exp "*" Exp               //<8>                               
   > left Exp "+" Exp               //<9>
   > "if" Exp "then" Exp "else" Exp //<10>
   ;   

keyword Reserved
    = "var" | "if" | "then" | "else"
    ;    