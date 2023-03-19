
axiom df-gbow
  let vz: setvar z
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- GoldbachOddW = { z e. Odd | E. p e. Prime E. q e. Prime E. r e. Prime z = ( ( p + q ) + r ) }
end
