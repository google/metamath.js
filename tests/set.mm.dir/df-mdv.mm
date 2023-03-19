
axiom df-mdv
  let vt: setvar t
  assert |- mDV = ( t e. _V |-> ( ( ( mVR ` t ) X. ( mVR ` t ) ) \ _I ) )
end
