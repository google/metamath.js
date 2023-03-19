
axiom df-btwn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vi: setvar i
  let vn: setvar n
  assert |- Btwn = `' { <. <. x , z >. , y >. | E. n e. NN ( ( x e. ( EE ` n ) /\ z e. ( EE ` n ) /\ y e. ( EE ` n ) ) /\ E. t e. ( 0 [,] 1 ) A. i e. ( 1 ... n ) ( y ` i ) = ( ( ( 1 - t ) x. ( x ` i ) ) + ( t x. ( z ` i ) ) ) ) }
end
