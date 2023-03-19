
axiom ax-ac2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  assert |- E. y A. z E. v A. u ( ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/ ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) )
end
