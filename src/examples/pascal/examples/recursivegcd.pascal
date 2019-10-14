{ program 11.9
  recursive formulation of gcd }
  
program recursivegcd(output);

var x,y,n : integer;

function gcd(m, n: integer) : integer;
begin if n=0 then gcd := m
      else gcd := gcd(n,m mod n)
end; {gcd}

procedure try(a,b : integer);
begin write(a,b, gcd(a,b))
end;

begin   try(18,27);
        try(312,21420);
        try(98,868)
end.