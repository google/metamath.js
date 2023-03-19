
axiom df-ust
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assert |- UnifOn = ( x e. _V |-> { u | ( u C_ ~P ( x X. x ) /\ ( x X. x ) e. u /\ A. v e. u ( A. w e. ~P ( x X. x ) ( v C_ w -> w e. u ) /\ A. w e. u ( v i^i w ) e. u /\ ( ( _I |` x ) C_ v /\ `' v e. u /\ E. w e. u ( w o. w ) C_ v ) ) ) } )
end
