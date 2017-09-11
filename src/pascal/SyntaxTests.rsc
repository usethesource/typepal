@license{
Copyright (c) 2017, Paul Klint, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module pascal::SyntaxTests

import pascal::Pascal;
import ParseTree;

bool p(type[&T<:Tree] begin, str s) {
    parse(begin, s);
    return true;
}

test bool Id1() =  p(#Identifier, "a");

test bool Id2() = p(#Identifier, "aB3");

test bool UI1() = p(#UnsignedInteger, "123");

test bool UR1() = p(#UnsignedReal, "12.34E5");

test bool Cons1() = p(#Constant, "123");
test bool Cons2() = p(#Constant, "123.45");
test bool Cons3() = p(#Constant, "123.45E6");
test bool Cons4() = p(#Constant, "123E6");

test bool Cons5() = p(#Constant, "+123");
test bool Cons6() = p(#Constant, "+123.45");
test bool Cons7() = p(#Constant, "+123.45E6");
test bool Cons8() = p(#Constant, "+123E6");

test bool Cons9()  = p(#Constant, "-123");
test bool Cons10() = p(#Constant, "-123.45");
test bool Cons11() = p(#Constant, "-123.45E6");
test bool Cons12() = p(#Constant, "-123E6");

test bool Cons13() = p(#Constant, "c");
test bool Cons14() = p(#Constant, "+c");
test bool Cons15() = p(#Constant, "-c");

test bool Cons16() = p(#Constant, "\'abc\'");

test bool ProgHeading1() = p(#ProgramHeading, "program P (f1);");
test bool ProgHeading2() = p(#ProgramHeading, "program P (f1,f2);");

test bool LabelDecl1() = p(#LabelDeclarationPart, "label 1;");
test bool LabelDecl2() = p(#LabelDeclarationPart, "label 1,2,3;");

test bool Type1() = p(#Type, "int");
test bool Type2() = p(#Type, "(int,int,real)");
test bool Type3() = p(#Type, "a..z");
test bool Type4() = p(#Type, "0..4");
test bool Type5() = p(#Type, "array[int] of real");
test bool Type6() = p(#Type, "array[int,real] of string");
test bool Type7() = p(#Type, "array[int] of real");

test bool Type8() = p(#Type, "record a : real end");
test bool Type8() = p(#Type, "record a : real; b : Boolean end");

test bool Type10() = p(#Type, "record subject: (history,language,lit,math,psych,science);
                                   assigned: date;
                                   grade: 0..4;
                                   weight: 1..10
                            end");

test bool Exp1() = p(#Expression, "1");
test bool Exp2() = p(#Expression, "1 + 2");
test bool Exp3() = p(#Expression, "1 + 2 * 3");
test bool Exp4() = p(#Expression, "1 mod 2");
test bool Exp5() = p(#Expression, "1 \<= 2");
test bool Exp6() = p(#Expression, "(x0 + x /x0)*0.5");
test bool Exp7() = p(#Expression, "abs(x1 - x0)");
test bool Exp7() = p(#Expression, "eps * x1");
test bool Exp7() = p(#Expression, "abs(x1 - x0) \< eps * x1");


//test bool FunDes1() = p(#FunctionDesignator, "f");
test bool FunDes2() = p(#FunctionDesignator, "f(1)");

test bool Set1() = p(#Set, "{}");
test bool Set2() = p(#Set, "{1}");
test bool Set3() = p(#Set, "{1,2}");

test bool AsgStat1()  = p(#AssignmentStatement, "x := 3");

test bool ProcStat1() = p(#ProcedureStatement, "p");
test bool ProcStat1() = p(#ProcedureStatement, "p(1)");

test bool GotoStat1() = p(#GoToStatement, "goto 3");

test bool IfStat1() = p(#IfStatement, "if b then x := 3");
test bool IfStat2() = p(#IfStatement, "if b then x := 3 else x := 4");

test bool CaseLabelList1() = p(#CaseLabelList, "1");
test bool CaseLabelList2() = p(#CaseLabelList, "1, 2");

test bool CaseListElem11() = p(#CaseListElement, "1: x := 3");
test bool CaseListElem12() = p(#CaseListElement, "1, 2: x := 3");

test bool CaseStat1() = p(#CaseStatement, "case e of 1: x := 3 end");

test bool RepStat1() = p(#RepetitiveStatement, "while n \> 0 do n := n - 1");
test bool RepStat2() = p(#RepetitiveStatement, "for n := 1 to 10 do x := 0");
test bool RepStat3() = p(#RepetitiveStatement, "for n := 10 downto 1 do x := 0");

test bool WithStat1() = p(#WithStatement, "with a, b, c do x := 0");

test bool VariableDeclarationPart1() =
    p(#VariableDeclarationPart,
    "var x0, x1: real;");

test bool CompoundStatement1() =
    p(#CompoundStatement,
    "begin x1 := x;
    '      repeat x := x0; x1 := (x0 + x /x0)*0.5
    '      until abs(x1 - x0) \< eps * x1;
    '      Sqrt := x0
    'end");

test bool Block1a(){ parse(#Block, "var x0, x1: real;
    'begin x1 := x;
    '      repeat x := x0; x1 := (x0 + x /x0)*0.5
    '      until abs(x1 - x0) \< eps * x1;
    '      Sqrt := x0
    'end");
    return true;
}
test bool Block1() =
    p(#Block, 
    "var x0, x1: real;
    'begin x1 := x;
    '      repeat x := x0; x1 := (x0 + x /x0)*0.5
    '      until abs(x1 - x0) \< eps * x1;
    '      Sqrt := x0
    'end");
    
test bool FunctionHeading1() =
    p(#FunctionHeading, 
    "function Sqrt(x : real) : real;");

test bool FunctionDeclaration1() = 
    p(#FunctionDeclaration,  
    "function Sqrt(x : real) : real;
    'var x0, x1: real;
    'begin x1 := x;
    '      repeat x := x0; x1 := (x0 + x /x0)*0.5
    '      until abs(x1 - x0) \< eps * x1;
    '      Sqrt := x0
    'end");
    
test bool FunctionDeclaration2() =
    p(#FunctionDeclaration,
    "function Max(a : vector; n : integer) : real;
    'var x : real; i : integer;
    'begin
    '   for i := 2 to n do
    '   begin
    '       if x \< a[i] then x := a[i]
    '   end;
    '   Max := x
    'end");

test bool FunctionDeclaration2() =
    p(#FunctionDeclaration,
    "function GCD(m,n : integer) : integer;
    'begin if n = 0 then GCD := m else GCD := GCD(n, m mod n)
    'end");
    
test bool FunctionDeclaration3() =
    p(#FunctionDeclaration,
    "function Power(x : real; y : integer) : real;
    'var w, z : real; i : integer;
    'begin w := x; z := 1; i := y;
    '   while i \> 0 do
    '   begin
    '       if odd(i) then z := z * w;
    '       i := i div 2;
    '       w := sqr(w);
    '   end;
    '   Power := z
    'end");