
axiom ax-inf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) )
end
