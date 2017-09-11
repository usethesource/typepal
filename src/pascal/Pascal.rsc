@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module pascal::Pascal

// Pascal (Pascal User Manual, Second Edition, 1978

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
   | @category="Comment" ws3: "{" ![\n}]*  "}"$
   ;

syntax Program =
   ProgramHeading programHeading Block block "."; 

syntax ProgramHeading =  
    "program" Identifier id "(" {FileIdentifier ","}+ fileIdentifiers ")" ";"; 

syntax FileIdentifier
    = Identifier
    ;
    
lexical Identifier
    = ([A-Za-z] [A-Za-z0-9]* !>> [A-Za-z0-9]) \ Reserved
    ;
    
keyword Reserved
    = "and" | "array" | "begin" | "case"     | "const"  | "div"       | "do"      | "downto" | "else"
    | "end" | "file"  | "for"   | "function" | "goto"   | "if"        | "in"      | "label"  | "mod"
    | "nil" | "not"   | "of"    | "or"       | "packed" | "procedure" | "program" | "record" | "repeat"
    | "set" | "then"  | "to"    | "type"     | "until"  | "var"       | "while"   | "with"
    ;
    
syntax Block
    =  LabelDeclarationPart? ConstantDefinitionPart? TypeDefinitionPart?
       VariableDeclarationPart? ProcedureAndFunctionDeclarationPart? StatementPart
    ;

syntax LabelDeclarationPart
    = "label" {Label ","}+  labels ";"
    ;

syntax Label
    = UnsignedInteger
    ;
    
syntax ConstantDefinitionPart
    = "const"  {ConstantDefinition ";"}+ ";"
    ;
    
syntax ConstantDefinition
    = Identifier id "=" Constant constant
    ;

syntax Constant
    = unumber: UnsignedNumber unsignedNumber
    | signednumber: Sign sign UnsignedNumber  unsignedNumber
    | constantid: ConstantIdentifier constantIdentifier
    | signedconstant: Sign sign ConstantIdentifier constantIdentifier
    | string: String string
    ;

lexical UnsignedNumber
    = integer: UnsignedInteger
    | \real: UnsignedReal
    ;
lexical UnsignedInteger
    = [0-9]+ !>> [0-9]
    ;
    
lexical UnsignedReal
    = UnsignedInteger "." UnsignedInteger
    | UnsignedInteger "." UnsignedInteger "E" ScaleFactor
    | UnsignedInteger "E" ScaleFactor
    ;
lexical ScaleFactor
    = UnsignedInteger
    | Sign UnsignedInteger
    ;

lexical Sign = "+" | "-";

syntax ConstantIdentifier
    = Identifier
    ;
lexical String
    = "\'" Character* "\'"
    ;

lexical Character
    = ![\']
    ;
syntax TypeDefinitionPart
    = "type"  {TypeDefinition ";"}+ ";"
    ;

syntax TypeDefinition
    = Identifier id "=" Type rtype
    ; 

syntax Type
    = simple: SimpleType simpleType  
    | structured: StructuredType structuredType  
    | pointer: "^" TypeIdentifier typeIdentifier
    ;

syntax SimpleType
    = scalar: ScalarType scalarType
    | subrange: SubrangeType  subrangeType
    | typeid: TypeIdentifier  typeIdentifier
    ;

syntax ScalarType
    = "("  {Identifier ","}+ ids ")"
    ;

syntax SubrangeType
    = Constant from ".." Constant to
    ;
syntax TypeIdentifier
    = Identifier
    ;

syntax StructuredType
    = unpacked: UnpackedStructuredType unpackedStructuredType
    | packed: "packed" UnpackedStructuredType unpackedStructuredType
    ;

syntax UnpackedStructuredType
    = array: ArrayType arrayType
    | record: RecordType recordType
    | \set: SetType setType
    | file: FileType fileType
    ;

syntax ArrayType    
    = "array" "[" {SimpleType ","}+ indexTypes "]" "of" Type rtype
    ;

syntax  RecordType
    = "record" FieldList fieldList "end" 
    ;
    
syntax FieldList
    = FixedPart  fixedPart
    | FixedPart fixedPart ";" VariantPart variantPart 
    | VariantPart variantPart 
    ;

syntax FixedPart
    = {RecordSection ";"}+ recordSections
    ; 

syntax RecordSection
    = {FieldIdentifier ","}+ fieldIdentifiers ":" Type rtype
    | ()
    ; 

syntax VariantPart
    = "case" TagField  TypeIdentifier "of" {Variant ";"}+ variantList 
    ;

syntax TagField
    = FieldIdentifier identifier ":"
    | ()
    ; 
syntax Variant
    = {CaseLabel ","}+ ":" "(" FieldList ")"
    | ()
    ;

syntax CaseLabel
    = Constant
    ;
    
syntax SetType
    = "set" "of" SimpleType simpleType  
    ;
    
syntax FileType
    = "file" "of" Type type  
    ;
    
syntax PointerType
    = "^" TypeIdentifier
    ;
    
syntax VariableDeclarationPart
    = "var" {VariableDeclaration ";"}+ ";"
    ;

syntax VariableDeclaration
    = {Identifier ","}+ ids ":" Type type
    ;
 
syntax ProcedureAndFunctionDeclarationPart
    =   ProcedureOrFunctionDeclaration+
    ;

syntax ProcedureOrFunctionDeclaration
    = ProcedureDeclaration ";"
    | FunctionDeclaration ";"
    ;
    
syntax ProcedureDeclaration
    = ProcedureHeading procedureHeading Block block
    ;
syntax ProcedureHeading
    = "procedure" Identifier id ";"
    | "procedure" Identifier id "(" {FormalParameterSection ";"}+ formals ")" ";"
    ;

syntax FormalParameterSection
    = ParameterGroup group
    | "var" ParameterGroup group
    | "function" ParameterGroup group
    | "procedure" {Identifier ","}+
    ;
syntax ParameterGroup
    = {Identifier ","}+ ids ":" Type rtype
    ;
syntax FunctionDeclaration
    = FunctionHeading functionHeading Block block
    ;
syntax FunctionHeading
    = "function" Identifier id ":" ResultType rtype ";"
    | "function" Identifier id "(" {FormalParameterSection ";"}+ formals ")" ":" ResultType rtype ";"
    ;

syntax ResultType
    = TypeIdentifier typeIdentifier
    ;

syntax StatementPart
    = CompoundStatement
    ;

syntax Statement
    = UnlabelledStatement unlabelledStatement
    | Label label ":" UnlabelledStatement unlabelledStatement
    ;
    
syntax UnlabelledStatement
    = SimpleStatement
    | StructuredStatement
    ;

syntax SimpleStatement
    = AssignmentStatement
    | ProcedureStatement
    | GoToStatement
    | EmptyStatement
    ;

syntax AssignmentStatement
    = Variable ":=" Expression  
//    | FunctionIdentifier ":=" Expression
    ;

syntax Variable
    = entire: EntireVariable
    | component: ComponentVariable
    | referenced: ReferencedVariable
    ;

syntax EntireVariable
    = VariableIdentifier
    ;
syntax VariableIdentifier
    = Identifier
    ;
syntax ComponentVariable
    = IndexedVariable
    | FieldDesignator
    | FileBuffer
    ;

syntax IndexedVariable
    = //ArrayVariable
      ArrayVariable "[" { Expression ","}+ "]"
    ;

syntax ArrayVariable
    = Variable
    ;
    
syntax FieldDesignator
    = RecordVariable "." FieldIdentifier
    ;    
syntax RecordVariable 
    = Variable variable
    ;

syntax FieldIdentifier 
    = Identifier
    ;
syntax FileBuffer
    = FileVariable "^" !>> "."
    ;

syntax FileVariable
    = Variable
    ;
syntax ReferencedVariable
    = PointerVariable "^"
    ;
syntax PointerVariable
    = Variable
    ;
    
syntax Expression
    = Variable
    | UnsignedConstant
    | "(" Expression ")"
    | FunctionDesignator
    | Set
   
    > left ( Expression "*" Expression
           | Expression "/" Expression
           | Expression "div" Expression
           | Expression "mod" Expression
           | Expression "and" Expression
           )           
    > left ( Expression "+" Expression
           | Expression "-" Expression
           | Expression "or" Expression
           )     
    | left ( Expression "=" Expression
           | Expression "\<\>" Expression
           | Expression "\<"  Expression
           | Expression "\<=" Expression
           | Expression "\>="  Expression
           | Expression  "\>" Expression
           | Expression "in" Expression
           )
    > non-assoc "not" Expression
    > non-assoc Sign Expression
    ;

syntax UnsignedConstant
    = unumber: UnsignedNumber unsignedNumber
    | string: String string
    //| ConstantIdentifier
    | nil: "nil"
    ;

syntax FunctionDesignator
    = //FunctionIdentifier
      FunctionIdentifier "(" { ActualParameter ","}+ ")"
    ;
    
syntax FunctionIdentifier
    = Identifier
    ;

syntax Set
    = "{" { Element ","}* "}"
    ;

syntax Element
    = Expression
    | Expression ".." Expression
    ;

syntax ProcedureStatement
    = ProcedureIdentifier
    | ProcedureIdentifier "(" {ActualParameter ","}+ ")"
    ;

syntax ProcedureIdentifier
    = Identifier
    ;
syntax ActualParameter
    = Expression
//    | Variable
//    | ProcedureIdentifier
//    | FunctionIdentifier
    ;

syntax GoToStatement
    = "goto" Label label
    ;

syntax EmptyStatement
    = ()
    ;
syntax StructuredStatement
    = CompoundStatement
    | ConditionalStatement
    | RepetitiveStatement
    | WithStatement
    ;

syntax CompoundStatement
    = "begin" { Statement ";" }+ "end"
    ;

syntax ConditionalStatement
    = IfStatement
    | CaseStatement
    ;

syntax IfStatement
    = "if" Expression condition "then" Statement () !>> "else" 
    | "if" Expression condition "then" Statement "else" Statement
    ;
syntax CaseStatement
    = "case" Expression "of" {CaseListElement ";"}+ "end"
    ;

syntax CaseListElement
    = CaseLabelList ":" Statement
    | ()
    ;

syntax CaseLabelList
    = { CaseLabel ","}+
    ;
    
syntax RepetitiveStatement
    = WhileStatement
    | RepeatStatement
    | ForStatement
    ;
 
syntax WhileStatement
    = "while" Expression condition "do" Statement
    ;
syntax RepeatStatement
    =  "repeat" {Statement ";"}+ "until" Expression condition
    ;

syntax ForStatement
    = "for" Identifier control ":=" ForList forList "do" Statement
    ;
    
syntax ForList
    = Expression initial "to" Expression final
    | Expression initial "downto" Expression final
    ;
    
syntax WithStatement
    = "with" {RecordVariable ","}+ "do" Statement
    ;
