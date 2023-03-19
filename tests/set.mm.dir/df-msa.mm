
axiom df-msa
  let vt: setvar t
  let va: setvar a
  assert |- mSA = ( t e. _V |-> { a e. ( mEx ` t ) | ( ( m0St ` a ) e. ( mAx ` t ) /\ ( 1st ` a ) e. ( mVT ` t ) /\ Fun ( `' ( 2nd ` a ) |` ( mVR ` t ) ) ) } )
end
