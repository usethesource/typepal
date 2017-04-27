module dtfun::GenerateBig

import IO;
    
str generate(int n) =
    "let inc1 : int -\> int = fun x : int { x + 1 } in
    '<for(int i <- [1 .. n]){>let inc<i+1> : int -\> int = fun x : int { if true then inc<i>(x) + 1 else inc<i>(x) + 1 fi } in
    '<}>
    'inc<n>(1)
    '<for(int i <- [1 .. n+1]){> end<}>";
 
 void main(){   
    writeFile(|project://TypePal/src/dtfun/big.dt|, generate(200));
}