
axiom df-msax
  let vt: setvar t
  let vp: setvar p
  assert |- mSAX = ( t e. _V |-> ( p e. ( mSA ` t ) |-> ( ( mVH ` t ) " ( ( mVars ` t ) ` p ) ) ) )
end
