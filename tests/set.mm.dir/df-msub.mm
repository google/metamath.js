
axiom df-msub
  let vt: setvar t
  let ve: setvar e
  let vf: setvar f
  assert |- mSubst = ( t e. _V |-> ( f e. ( ( mREx ` t ) ^pm ( mVR ` t ) ) |-> ( e e. ( mEx ` t ) |-> <. ( 1st ` e ) , ( ( ( mRSubst ` t ) ` f ) ` ( 2nd ` e ) ) >. ) ) )
end
