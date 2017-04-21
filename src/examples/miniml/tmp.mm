let inc1 = \x . (x + 1) in
let inc2 = \x . if true then (inc1 x) else 1 fi in
(inc2 3)