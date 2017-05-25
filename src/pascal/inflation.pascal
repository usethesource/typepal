program inflation(output);

const n = 10;
var i : integer; w1,w2,w3 : real;
begin i := 0; w1 := 1.0; w2 := 1.0; w3 := 1.0;
    repeat
        i := i + 1;
            w1 := w1 * 1.07;
            w2 := w2 * 1.08;
            w3 := w3 * 1.10;
            writeln(i,w1,w2,w3)
    until i=n
end.