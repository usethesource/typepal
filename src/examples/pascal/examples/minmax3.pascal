{program 11.2
 extend proqram 11.1 }
 
program minmax3(input,output) ;
const n = 20;
type list = array[ 1..n] of integer;
var a,b :list;
    i,j,min1,min2,max1,max2 : integer;

procedure minmax(var g:list ; var j,k :integer) ;
    var i : 1..n; u,v : integer;
begin j:=g[1]; k:=j; i:=2;
    while i<n do
    begin u:=g[i] ;v:=g[i+1] ;
        if u>v then
        begin if u>k then k := u ;
              if v<j then j:=v
        end else 
        begin if v>k then k := v;
              if u<j then j := u
        end;
        i := i+2 
    end;
    if i=n then
        if g[n]>k then k := g[n]
        else if g[n] <j then j := g[n] ;
end; {minmax}

begin {read array}
    for i := 1 to n do
        begin read(a[i] ); write(a[i]) end; { :3}
        writeln ;
        minmax (a,min1,max1);
        writeln(min1,max1,max1-min1) ; writeln; 
        for i := 1 to n do
            begin read(b[i]); write(b[i]) end; { :3}
        writeln;
        minmax (b,min2,max2) ;
        writeln(min2,max2,max2-min2);
        writeln(abs (min1-min2) ,abs (max1-max2)); writeln ;
        for i := 1 to n do
            begin a[i] := a[i] + b[i]; write(a[i]) end; { :5}
        writeln ;
        minmax (a ,min1,max1);
        writeln (min1,max1, max1-min1) 
end.
