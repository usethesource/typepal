program person(input,output);
type link = ^person;
     person = record name : string; ss : integer; next : link end;
var first, p : link; i, n, s : integer;      
begin
    first := nil;
    for i := 1 to n do
    begin read(s); new(p);
        p^.next := first;
        p^.ss := s;
        first := p
    end
end.