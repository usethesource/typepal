@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::picoci::Syntax
  
// Pico, a trivial, classic, language:
// - single scope, no functions
// - integers and strings as types and values
// - assignment, if and while statements

lexical Id  = [a-zA-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9];
lexical Natural = [0-9]+ ;
lexical String = "\"" ![\"]*  "\"";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "%" ![%]+ "%"
   ;
 
start syntax Program 
   = program: 'begin' Declarations decls {Statement  ";"}* body 'end'
   ;

syntax Declarations 
   = 'declare' {Declaration ","}* decls ";" ;  
 
syntax Declaration 
    = decl: Id id ":" Type tp
    ;  
 
syntax Type 
   = 'natural' 
   | 'string'
   ;

syntax Statement 
   = Id var ":=" Expression val                                                                      
   | 'if' Expression cond 'then' {Statement ";"}*  thenPart 'else' {Statement ";"}* elsePart 'fi'   
   | 'while' Expression cond 'do' {Statement ";"}* body 'od'                                   
   ;  
      
syntax Expression 
   = Id name                                    
   | String string                          
   | Natural natcon                         
   | bracket "(" Expression e ")"                   
   > left ( Expression lhs "+" Expression rhs                                          
          | Expression lhs "-" Expression rhs  
          )
   ;

