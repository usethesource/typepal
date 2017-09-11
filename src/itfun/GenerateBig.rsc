@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module itfun::GenerateBig

import IO;

str generate1(int n) =
    "let inc1 = fun x { x + 1 } in
    '<for(int i <- [1 .. n]){>let inc<i+1> = fun x { inc<i>(x) } in
    '<}>
    'inc<n>(1)
    '<for(int i <- [1 .. n]+1){> end<}>";
    
str generate2(int n) =
    "let inc1 = fun x { x + 1 } in
    '<for(int i <- [1 .. n]){>let inc<i+1> = fun x { if true then inc<i>(x) + 1 else inc<i>(x) + 1 fi } in
    '<}>
    'inc<n>(1)
    '<for(int i <- [1 .. n+1]){> end<}>";
 
 void main(){   
    writeFile(|project://TypePal/src/itfun/big.it|, generate2(200));
}
