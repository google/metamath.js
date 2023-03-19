
axiom df-ifs
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assert |- InnerFiveSeg = { <. p , q >. | E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n ) E. d e. ( EE ` n ) E. x e. ( EE ` n ) E. y e. ( EE ` n ) E. z e. ( EE ` n ) E. w e. ( EE ` n ) ( p = <. <. a , b >. , <. c , d >. >. /\ q = <. <. x , y >. , <. z , w >. >. /\ ( ( b Btwn <. a , c >. /\ y Btwn <. x , z >. ) /\ ( <. a , c >. Cgr <. x , z >. /\ <. b , c >. Cgr <. y , z >. ) /\ ( <. a , d >. Cgr <. x , w >. /\ <. c , d >. Cgr <. z , w >. ) ) ) }
end
