{ program 6.3
  matrix multiplication }

program matrixmul(input, output);

const   m = 4; p = 3; n = 2;
var     i : 1..m; j : 1..m; k : 1..p;
        s : integer;
        a : array[1..m,1..n] of integer;
        b : array[1..p, 1..n] of integer;
        c : array[1..m, 1..n] of integer;

begin { assign initial value to a and b}
    for i := 1 to m do
    begin for k := 1 to p do
          begin read(s); write(s); a[i,k] := s;
          end;
          writeln
    end;
    writeln;
    for k := 1 to n do
    begin for j := 1 to n do
          begin read(s); write(s); b[k,j] := s
          end;
          writeln
    end;
    writeln;
    {multiply a*b}
    for i := 1 to m do
    begin for j := 1 to n do
          begin s := 0;
            for k := 1 to p do s := s + a[i,k]*b[k,j];
            c[i,j] := s; write(s)
          end;
          writeln
    end;
    writeln;
end.