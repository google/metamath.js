
axiom df-mfitp
  let vv: setvar v
  let vt: setvar t
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  assert |- mFromItp = ( t e. _V |-> ( f e. X_ a e. ( mSA ` t ) ( ( ( mUV ` t ) " { ( ( 1st ` t ) ` a ) } ) ^m X_ i e. ( ( mVars ` t ) ` a ) ( ( mUV ` t ) " { ( ( mType ` t ) ` i ) } ) ) |-> ( iota_ n e. ( ( mUV ` t ) ^pm ( ( mVL ` t ) X. ( mEx ` t ) ) ) A. m e. ( mVL ` t ) ( A. v e. ( mVR ` t ) <. m , ( ( mVH ` t ) ` v ) >. n ( m ` v ) /\ A. e A. a A. g ( e ( mST ` t ) <. a , g >. -> <. m , e >. n ( f ` ( i e. ( ( mVars ` t ) ` a ) |-> ( m n ( g ` ( ( mVH ` t ) ` i ) ) ) ) ) ) /\ A. e e. ( mEx ` t ) ( n " { <. m , e >. } ) = ( ( n " { <. m , ( ( mESyn ` t ) ` e ) >. } ) i^i ( ( mUV ` t ) " { ( 1st ` e ) } ) ) ) ) ) )
end
