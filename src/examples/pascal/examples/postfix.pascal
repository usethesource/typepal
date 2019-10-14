{ program 11.4
  conversion to postfix form }
program postfix(input,output); 

var ch : char ;
procedure find;
begin repeat read(ch)
      until (ch<> ' ') and not eoln(input)
end ;

procedure expression;
    var op : char;
    
    procedure term;
    
    procedure factor;
    begin if ch = '(' then
        begin find; expression;
        end else write(ch);
        find
    end; {factor}
    
    begin factor;
        while ch='*' do
        begin find; factor; write('*')
        end
    end; {term}
    
begin term;
    while (ch='+') or (ch='-') do
        begin op := ch; find; term; write(op)
        end
end; {expression}

begin find;
    repeat write(' ');
        expression;
        writeln;
    until ch ='.'
end.
 