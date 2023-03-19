
axiom df-mcls
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vh: setvar h
  let vm: setvar m
  let vo: setvar o
  let vs: setvar s
  let vp: setvar p
  let vc: setvar c
  let vd: setvar d
  assert |- mCls = ( t e. _V |-> ( d e. ~P ( mDV ` t ) , h e. ~P ( mEx ` t ) |-> |^| { c | ( ( h u. ran ( mVH ` t ) ) C_ c /\ A. m A. o A. p ( <. m , o , p >. e. ( mAx ` t ) -> A. s e. ran ( mSubst ` t ) ( ( ( s " ( o u. ran ( mVH ` t ) ) ) C_ c /\ A. x A. y ( x m y -> ( ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` x ) ) ) X. ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` y ) ) ) ) C_ d ) ) -> ( s ` p ) e. c ) ) ) } ) )
end
