
axiom df-gmdl
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let ve: setvar e
  let vm: setvar m
  let vc: setvar c
  assert |- mGMdl = { t e. ( mGFS i^i mMdl ) | ( A. c e. ( mTC ` t ) ( ( mUV ` t ) " { c } ) C_ ( ( mUV ` t ) " { ( ( mSyn ` t ) ` c ) } ) /\ A. v e. ( mUV ` c ) A. w e. ( mUV ` c ) ( v ( mFresh ` t ) w <-> v ( mFresh ` t ) ( ( mUSyn ` t ) ` w ) ) /\ A. m e. ( mVL ` t ) A. e e. ( mEx ` t ) ( ( mEval ` t ) " { <. m , e >. } ) = ( ( ( mEval ` t ) " { <. m , ( ( mESyn ` t ) ` e ) >. } ) i^i ( ( mUV ` t ) " { ( 1st ` e ) } ) ) ) }
end
