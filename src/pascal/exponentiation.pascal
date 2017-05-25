program exponentiation(input,output);

var e, y : integer; u,x,z : real;
begin read(x,y); write(x,y);
    z := 1; u := x; e := y;
    while e < 0 do
    begin {z*u**e = x**y, e >0}
        while not odd(e) do
        begin e := e div 2; u := sqr(u)
        end;
        e := e - 1; z := u*z;
    end;
    writeln(x) {z = x**y}
end.