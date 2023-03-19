
axiom df-mitp
  let vx: setvar x
  let vt: setvar t
  let vg: setvar g
  let vi: setvar i
  let vm: setvar m
  let va: setvar a
  assert |- mItp = ( t e. _V |-> ( a e. ( mSA ` t ) |-> ( g e. X_ i e. ( ( mVars ` t ) ` a ) ( ( mUV ` t ) " { ( ( mType ` t ) ` i ) } ) |-> ( iota x E. m e. ( mVL ` t ) ( g = ( m |` ( ( mVars ` t ) ` a ) ) /\ x = ( m ( mEval ` t ) a ) ) ) ) ) )
end
