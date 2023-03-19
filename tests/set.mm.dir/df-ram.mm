
axiom df-ram
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vr: setvar r
  let vc: setvar c
  assert |- Ramsey = ( m e. NN0 , r e. _V |-> inf ( { n e. NN0 | A. s ( n <_ ( # ` s ) -> A. f e. ( dom r ^m { y e. ~P s | ( # ` y ) = m } ) E. c e. dom r E. x e. ~P s ( ( r ` c ) <_ ( # ` x ) /\ A. y e. ~P x ( ( # ` y ) = m -> ( f ` y ) = c ) ) ) } , RR* , < ) )
end
