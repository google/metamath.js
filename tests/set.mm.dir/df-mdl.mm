
axiom df-mdl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let ve: setvar e
  let vf: setvar f
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vp: setvar p
  let va: setvar a
  let vd: setvar d
  assert |- mMdl = { t e. mFS | [. ( mUV ` t ) / u ]. [. ( mEx ` t ) / x ]. [. ( mVL ` t ) / v ]. [. ( mEval ` t ) / n ]. [. ( mFresh ` t ) / f ]. ( ( u C_ ( ( mTC ` t ) X. _V ) /\ f e. ( mFRel ` t ) /\ n e. ( u ^pm ( v X. ( mEx ` t ) ) ) ) /\ A. m e. v ( ( A. e e. x ( n " { <. m , e >. } ) C_ ( u " { ( 1st ` e ) } ) /\ A. y e. ( mVR ` t ) <. m , ( ( mVH ` t ) ` y ) >. n ( m ` y ) /\ A. d A. h A. a ( <. d , h , a >. e. ( mAx ` t ) -> ( ( A. y A. z ( y d z -> ( m ` y ) f ( m ` z ) ) /\ h C_ ( dom n " { m } ) ) -> m dom n a ) ) ) /\ ( A. s e. ran ( mSubst ` t ) A. e e. ( mEx ` t ) A. y ( <. s , m >. ( mVSubst ` t ) y -> ( n " { <. m , ( s ` e ) >. } ) = ( n " { <. y , e >. } ) ) /\ A. p e. v A. e e. x ( ( m |` ( ( mVars ` t ) ` e ) ) = ( p |` ( ( mVars ` t ) ` e ) ) -> ( n " { <. m , e >. } ) = ( n " { <. p , e >. } ) ) /\ A. y e. u A. e e. x ( ( m " ( ( mVars ` t ) ` e ) ) C_ ( f " { y } ) -> ( n " { <. m , e >. } ) C_ ( f " { y } ) ) ) ) ) }
end
