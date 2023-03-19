
axiom df-trkg2d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vd: setvar d
  assert |- TarskiG2D = { f | [. ( Base ` f ) / p ]. [. ( dist ` f ) / d ]. [. ( Itv ` f ) / i ]. ( E. x e. p E. y e. p E. z e. p -. ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) ) /\ A. x e. p A. y e. p A. z e. p A. u e. p A. v e. p ( ( ( ( x d u ) = ( x d v ) /\ ( y d u ) = ( y d v ) /\ ( z d u ) = ( z d v ) ) /\ u =/= v ) -> ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) ) ) ) }
end
