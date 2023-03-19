
axiom df-segle
  let vy: setvar y
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assert |- Seg<_ = { <. p , q >. | E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n ) E. d e. ( EE ` n ) ( p = <. a , b >. /\ q = <. c , d >. /\ E. y e. ( EE ` n ) ( y Btwn <. c , d >. /\ <. a , b >. Cgr <. c , y >. ) ) }
end
