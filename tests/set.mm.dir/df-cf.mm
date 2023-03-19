
axiom df-cf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  assert |- cf = ( x e. On |-> |^| { y | E. z ( y = ( card ` z ) /\ ( z C_ x /\ A. v e. x E. u e. z v C_ u ) ) } )
end
