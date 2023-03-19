
axiom df-mvl
  let vv: setvar v
  let vt: setvar t
  assert |- mVL = ( t e. _V |-> X_ v e. ( mVR ` t ) ( ( mUV ` t ) " { ( ( mType ` t ) ` v ) } ) )
end
