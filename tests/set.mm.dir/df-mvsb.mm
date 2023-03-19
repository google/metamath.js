
axiom df-mvsb
  let vx: setvar x
  let vv: setvar v
  let vt: setvar t
  let vm: setvar m
  let vs: setvar s
  assert |- mVSubst = ( t e. _V |-> { <. <. s , m >. , x >. | ( ( s e. ran ( mSubst ` t ) /\ m e. ( mVL ` t ) ) /\ A. v e. ( mVR ` t ) m dom ( mEval ` t ) ( s ` ( ( mVH ` t ) ` v ) ) /\ x = ( v e. ( mVR ` t ) |-> ( m ( mEval ` t ) ( s ` ( ( mVH ` t ) ` v ) ) ) ) ) } )
end
