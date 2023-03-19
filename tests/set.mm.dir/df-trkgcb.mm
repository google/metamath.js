
axiom df-trkgcb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assert |- TarskiGCB = { f | [. ( Base ` f ) / p ]. [. ( dist ` f ) / d ]. [. ( Itv ` f ) / i ]. ( A. x e. p A. y e. p A. z e. p A. u e. p A. a e. p A. b e. p A. c e. p A. v e. p ( ( ( x =/= y /\ y e. ( x i z ) /\ b e. ( a i c ) ) /\ ( ( ( x d y ) = ( a d b ) /\ ( y d z ) = ( b d c ) ) /\ ( ( x d u ) = ( a d v ) /\ ( y d u ) = ( b d v ) ) ) ) -> ( z d u ) = ( c d v ) ) /\ A. x e. p A. y e. p A. a e. p A. b e. p E. z e. p ( y e. ( x i z ) /\ ( y d z ) = ( a d b ) ) ) }
end
