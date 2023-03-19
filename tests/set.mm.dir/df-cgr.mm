
axiom df-cgr
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vn: setvar n
  assert |- Cgr = { <. x , y >. | E. n e. NN ( ( x e. ( ( EE ` n ) X. ( EE ` n ) ) /\ y e. ( ( EE ` n ) X. ( EE ` n ) ) ) /\ sum_ i e. ( 1 ... n ) ( ( ( ( 1st ` x ) ` i ) - ( ( 2nd ` x ) ` i ) ) ^ 2 ) = sum_ i e. ( 1 ... n ) ( ( ( ( 1st ` y ) ` i ) - ( ( 2nd ` y ) ` i ) ) ^ 2 ) ) }
end
