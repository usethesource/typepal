@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::fwjava::Syntax

// FeatherWeightJava

// ----  syntax ---------------------------------------------------------------

lexical ClassId  = ([A-Z][A-Zåa-z0-9]* !>> [a-z0-9]) \ Reserved;
lexical Id       = ([a-z][a-z0-9]* !>> [a-z0-9]) \ Reserved;

keyword Reserved = "class" | "extends" | "this" | "return";

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "%" ![%]+ "%"
   ;
   
start syntax FWJProgram
    = ClassDecl* classdecls
    ;
    
syntax ClassDecl
    = "class" ClassId cid "extends" ClassId ecid "{" 
              FieldDecl* fielddecls
              ConstructorDecl constructordecl
              MethodDecl* methoddecls
        "}"
     ;

syntax FieldDecl
    = ClassId cid Id id ";"
    ;

syntax ConstructorDecl
    =  ClassId cid Formals formals "{"
            SuperCall supercall
            FieldAssignment* fieldAssignments
       "}"
    ;

syntax SuperCall
    = "super" super "(" {Variable ","}* vars ")" ";"
    ;
    
syntax Formal
    =  ClassId cid Id id
    ;
    
syntax Formals
    = "(" {Formal ","}* formals ")"
    ;
          
syntax MethodDecl
    = ClassId cid Id mid Formals formals "{" "return" Expression exp ";" "}"
    ;
    
syntax Expression
    = Variable var
    | Expression exp "." Field field
    | Expression exp "." Method method Expressions exps
    | "new" Constructor constructor Expressions exps
    | "(" Class class ")" Expression exp
    | "this"
    ;

syntax Constructor
    = ClassId id
    ;
syntax Class
    = ClassId id
    ;
    
syntax Variable
    = Id id
    ;
 
syntax Field
    = Id id
    ;

syntax Method
    = Id id
    ;
           
syntax Expressions
    = "(" {Expression ","}* expressions ")"
    ;   

syntax FieldAssignment
    = "this" "." Field field "=" Expression exp ";"
    ;   
