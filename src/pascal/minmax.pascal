program minmax(input,output);

const n = 20;
var i,u,v,min,max: integer;
    a : array[1..n] of integer;
begin
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
       begin %% this begin end is needed to get this parsed
       if a[n] > max then max := a[n]
       else if a[n] < min then min := a[n]
       end;
    writeln(max, min)
end.