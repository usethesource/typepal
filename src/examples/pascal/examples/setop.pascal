{ program 8.1 
  example of set operations }

program setop(output);

type days = (m,t,w,th,fr,sa,su);
     week = set of days;
 var wk, work, free : week;
     d : days;
     
procedure check(s : week);
var d : days;
begin write(' ');
    for d := m to su do
        if d in s then write('x') else write('o');
    writeln
end; {check}

begin work := []; free := [];
    wk := [m..su];
    d := sa; free := [d] + free + [su];
    check(free);
    work := wk - free; check(work);
    if free <= wk then write(' o');
    if wk >= work then write('k');
    if not(work >= free) then write(' jack');
    if [sa] <= work then write(' forget it');
    writeln
 end.