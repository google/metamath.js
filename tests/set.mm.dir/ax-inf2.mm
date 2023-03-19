
axiom ax-inf2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- E. x ( E. y ( y e. x /\ A. z -. z e. y ) /\ A. y ( y e. x -> E. z ( z e. x /\ A. w ( w e. z <-> ( w e. y \/ w = y ) ) ) ) )
end
