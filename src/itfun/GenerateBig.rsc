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