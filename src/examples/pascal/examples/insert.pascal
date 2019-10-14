{ program 9.1 -- insert leading blanks }

program insert(input,output);

var ch : char;
begin
    while not eof do
    begin write(' ');
        while not eoln do
            begin read(ch); write(ch)
            end;
        writeln; readln
    end
 end.