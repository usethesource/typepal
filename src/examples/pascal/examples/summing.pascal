{ program 4.6
  compute 1 - 1/2 + 1/3-...+1/9999 - 1/10000 in 4 ways.
  1) left to right in succession
  2) left to right, all pos and neg terms, then subtract
  3) right to left in succession
  4) right to left, all pos and neg terms, then subtract}

program summing(output);

var s1, s2p, s2n, s3, s4p, s4n, lrp, lrn, rlp, rln : real;
    i : integer;
begin s1 := 0; s2p := 0; s2n := 0; s3 := 0; s4p := 0; s4n := 0;
    for i := 1 to 5000 do
    begin
        lrp := 1/(2*i-1); { pos terms, left to right }
        lrn := 1/(2*i); { neg term, left to right }
        rlp := 1/(10001-2*i); { pos terms, right to left }
        rln := 1/(10002-2*i); { neg terms, right to left }
        s1 := s1 + lrp - lrn;
        s2p := s2p + lrp; s2n := s2n + lrn;
        s3 := s3 + rlp - rln;
        s4p := s4p + rlp; s4n := s4n + rln;
    end;
    writeln(s1,s2p-s2n);
    writeln(s3,s4p-s4n);
end.