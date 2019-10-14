{ program 9.1 -- frequency count of letters in input file }

program fcount(input, output);

var ch : char;
    count: array['a'..'z'] of integer;
    letter: set of 'a'..'z';
begin letter := ['a'..'z'];
    for ch := 'a' to 'z' do count[ch] := 0;
    while not eof do
    begin
        while not eoln do
        begin read(ch); write(ch);
            if ch in letter then count[ch] := count[ch] + 1;
        end;
        writeln; readln
    end
 end.