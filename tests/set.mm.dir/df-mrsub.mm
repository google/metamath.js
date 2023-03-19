
axiom df-mrsub
  let vv: setvar v
  let vt: setvar t
  let ve: setvar e
  let vf: setvar f
  assert |- mRSubst = ( t e. _V |-> ( f e. ( ( mREx ` t ) ^pm ( mVR ` t ) ) |-> ( e e. ( mREx ` t ) |-> ( ( freeMnd ` ( ( mCN ` t ) u. ( mVR ` t ) ) ) gsum ( ( v e. ( ( mCN ` t ) u. ( mVR ` t ) ) |-> if ( v e. dom f , ( f ` v ) , <" v "> ) ) o. e ) ) ) ) )
end
