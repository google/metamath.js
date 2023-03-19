
axiom df-linc
  let vx: setvar x
  let vv: setvar v
  let vm: setvar m
  let vs: setvar s
  assert |- linC = ( m e. _V |-> ( s e. ( ( Base ` ( Scalar ` m ) ) ^m v ) , v e. ~P ( Base ` m ) |-> ( m gsum ( x e. v |-> ( ( s ` x ) ( .s ` m ) x ) ) ) ) )
end
