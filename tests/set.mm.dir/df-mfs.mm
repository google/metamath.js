
axiom df-mfs
  let vv: setvar v
  let vt: setvar t
  assert |- mFS = { t | ( ( ( ( mCN ` t ) i^i ( mVR ` t ) ) = (/) /\ ( mType ` t ) : ( mVR ` t ) --> ( mTC ` t ) ) /\ ( ( mAx ` t ) C_ ( mStat ` t ) /\ A. v e. ( mVT ` t ) -. ( `' ( mType ` t ) " { v } ) e. Fin ) ) }
end
