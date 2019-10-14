{ program 6.2
  extend program 4.9 to print x-axis }

program graph2(output);
const   d = 0.0625; { 1/16, 16 lines for interval [x,x+1]}
        s = 32;     { 32 character width for interval [y,y+1]}
        h1 = 34;    { character position of x-axis}
        h2 = 68;    { line width }
        c = 6.28318; { 2*pi }
        lim = 32;
var i, j, k, n : integer; x, y : real;
    a : array[1..h2] of char;
begin for j := 0 to h2 do a[j] := ' ';
    for i := 0 to lim do
        begin x := d*i; y := exp(-x)*sin(c*x);
        a[h1] := ':';  n := round(s*y) + h1; a[n] := '*';
        if n < h1 then k := h1 else k := n;
        for j := i to k do write(a[j]);
        writeln; a[n] := ' ';
    end
end.