
axiom df-gbo
  let vz: setvar z
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- GoldbachOdd = { z e. Odd | E. p e. Prime E. q e. Prime E. r e. Prime ( ( p e. Odd /\ q e. Odd /\ r e. Odd ) /\ z = ( ( p + q ) + r ) ) }
end
