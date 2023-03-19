
axiom df-trkge
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
  assert |- TarskiGE = { f | [. ( Base ` f ) / p ]. [. ( Itv ` f ) / i ]. A. x e. p A. y e. p A. z e. p A. u e. p A. v e. p ( ( u e. ( x i v ) /\ u e. ( y i z ) /\ x =/= u ) -> E. a e. p E. b e. p ( y e. ( x i a ) /\ z e. ( x i b ) /\ v e. ( a i b ) ) ) }
end
