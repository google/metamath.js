
axiom df-line2
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vl: setvar l
  assert |- Line = { <. <. a , b >. , l >. | E. n e. NN ( ( a e. ( EE ` n ) /\ b e. ( EE ` n ) /\ a =/= b ) /\ l = [ <. a , b >. ] `' Colinear ) }
end
