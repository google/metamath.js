
axiom ax-groth
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assert |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\ E. w e. y A. v ( v C_ z -> v e. w ) ) /\ A. z ( z C_ y -> ( z ~~ y \/ z e. y ) ) )
end
