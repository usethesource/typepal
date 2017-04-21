module examples::miniml::GenerateBig

import IO;

str generate1(int n) =
    "let inc1 = \\x . (x + 1) in
    '<for(int i <- [1 .. n]){>let inc<i+1> = \\x . (inc<i> x) in
    '<}>
    '(inc<n> 1)";
    
str generate2(int n) =
    "let inc1 = \\x . (x + 1) in
    '<for(int i <- [1 .. n]){>let inc<i+1> = \\x . if true then (inc<i> x) + 1 else (inc<i> x) + 1 fi in
    '<}>
    '(inc<n> 1)";
 
 void main(){   
    writeFile(|project://TypePal/src/examples/miniml/big.mm|, generate2(200));
}