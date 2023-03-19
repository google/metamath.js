
axiom df-fs
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
  assert |- FiveSeg = { <. p , q >. | E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n ) E. d e. ( EE ` n ) E. x e. ( EE ` n ) E. y e. ( EE ` n ) E. z e. ( EE ` n ) E. w e. ( EE ` n ) ( p = <. <. a , b >. , <. c , d >. >. /\ q = <. <. x , y >. , <. z , w >. >. /\ ( a Colinear <. b , c >. /\ <. a , <. b , c >. >. Cgr3 <. x , <. y , z >. >. /\ ( <. a , d >. Cgr <. x , w >. /\ <. b , d >. Cgr <. y , w >. ) ) ) }
end
