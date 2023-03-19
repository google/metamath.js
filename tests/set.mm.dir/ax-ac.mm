
axiom ax-ac
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  assert |- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) )
end
