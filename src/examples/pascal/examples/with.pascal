program person(input,output);
type date = record day: 1..31;
                   month: 1..12;
                   year: integer
            end;
var d : date;
begin
    with      d    do
        if month = 12 then
            begin month := 1; year := year + 1
            end
        else month := month + 1
end.