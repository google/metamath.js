
axiom df-colinear
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assert |- Colinear = `' { <. <. b , c >. , a >. | E. n e. NN ( ( a e. ( EE ` n ) /\ b e. ( EE ` n ) /\ c e. ( EE ` n ) ) /\ ( a Btwn <. b , c >. \/ b Btwn <. c , a >. \/ c Btwn <. a , b >. ) ) }
end
