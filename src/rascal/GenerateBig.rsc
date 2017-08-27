module rascal::GenerateBig

import IO;
    
str generate(int n) =
    "module rascal::Big
    'void f(){
    '<for(int i <- [1 .. n]){> l<i> = []; m<i> = l<i>; l<i> = l<i> + 1.5;
    '<}>}";
 
 void generate(){   
    writeFile(|project://TypePal/src/rascal/Big.rsc|, generate(200));
}
void main() { generate(); }