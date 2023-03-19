
axiom df-lco
  let vv: setvar v
  let vm: setvar m
  let vs: setvar s
  let vc: setvar c
  assert |- LinCo = ( m e. _V , v e. ~P ( Base ` m ) |-> { c e. ( Base ` m ) | E. s e. ( ( Base ` ( Scalar ` m ) ) ^m v ) ( s finSupp ( 0g ` ( Scalar ` m ) ) /\ c = ( s ( linC ` m ) v ) ) } )
end
