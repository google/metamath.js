
axiom df-mtree
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let ve: setvar e
  let vh: setvar h
  let vm: setvar m
  let vo: setvar o
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  let vd: setvar d
  assert |- mTree = ( t e. _V |-> ( d e. ~P ( mDV ` t ) , h e. ~P ( mEx ` t ) |-> |^| { r | ( A. e e. ran ( mVH ` t ) e r <. ( m0St ` e ) , (/) >. /\ A. e e. h e r <. ( ( mStRed ` t ) ` <. d , h , e >. ) , (/) >. /\ A. m A. o A. p ( <. m , o , p >. e. ( mAx ` t ) -> A. s e. ran ( mSubst ` t ) ( A. x A. y ( x m y -> ( ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` x ) ) ) X. ( ( mVars ` t ) ` ( s ` ( ( mVH ` t ) ` y ) ) ) ) C_ d ) -> ( { ( s ` p ) } X. X_ e e. ( o u. ( ( mVH ` t ) " U. ( ( mVars ` t ) " ( o u. { p } ) ) ) ) ( r " { ( s ` e ) } ) ) C_ r ) ) ) } ) )
end
