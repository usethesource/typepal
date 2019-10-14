{ program part 6.1
  find the largest and smallest number in a given list }
  
program minmax(input,output);

const n = 20;
var i,u,v,min,max: integer;
    a : array[1..n] of integer;
begin
    { assume that at this point in the program, array a
      contains the values: 35 68 94 7 88 -5 -3 12 35 9
      -6 3 0 -2 74 88 52 43 5 4}
    min := a[1]; max := min; i := 2;
    while i < n do
    begin u := a[i]; v := a[i+1];
        if u > v then 
        begin if u > max then max := u;
              if v < min then min := v
        end else
        begin if v > max then max := v;
              if u < min then min := u
        end;
        i := i + 2
    end;
    if i = n then
       begin
       if a[n] > max then max := a[n]
       else if a[n] < min then min := a[n]
       end;
    writeln(max, min)
end.