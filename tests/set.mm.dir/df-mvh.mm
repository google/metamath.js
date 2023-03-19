
axiom df-mvh
  let vv: setvar v
  let vt: setvar t
  assert |- mVH = ( t e. _V |-> ( v e. ( mVR ` t ) |-> <. ( ( mType ` t ) ` v ) , <" v "> >. ) )
end
