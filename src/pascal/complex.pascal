program complex(output);
const fac = 4;
type complex = record re, im : integer end;
var x, y : complex;
    n : integer;
begin
    x.re := 2; x.im := 2;
    y.re := 6; y.im := 3;
    for n := 1 to 4 do
    begin
        writeln(' x = ', x.re, x.im, ' y = ', y.re, y.im);
        { x + y }
        writeln(' sum = ', x.re + y.re, x.im + y.im);
        { x * y }
        writeln(' product ', x.re*y.re - x.im*y.im,
                             x.re*y.im + x.im*y.re);
        x.re := x.re + fac; x.im := x.im - fac;
    end
end.