
axiom ax-pr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- E. z A. w ( ( w = x \/ w = y ) -> w e. z )
end
