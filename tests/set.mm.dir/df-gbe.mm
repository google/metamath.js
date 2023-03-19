
axiom df-gbe
  let vz: setvar z
  let vq: setvar q
  let vp: setvar p
  assert |- GoldbachEven = { z e. Even | E. p e. Prime E. q e. Prime ( p e. Odd /\ q e. Odd /\ z = ( p + q ) ) }
end
