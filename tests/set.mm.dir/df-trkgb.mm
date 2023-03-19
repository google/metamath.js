
axiom df-trkgb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let vf: setvar f
  let vi: setvar i
  let vs: setvar s
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- TarskiGB = { f | [. ( Base ` f ) / p ]. [. ( Itv ` f ) / i ]. ( A. x e. p A. y e. p ( y e. ( x i x ) -> x = y ) /\ A. x e. p A. y e. p A. z e. p A. u e. p A. v e. p ( ( u e. ( x i z ) /\ v e. ( y i z ) ) -> E. a e. p ( a e. ( u i y ) /\ a e. ( v i x ) ) ) /\ A. s e. ~P p A. t e. ~P p ( E. a e. p A. x e. s A. y e. t x e. ( a i y ) -> E. b e. p A. x e. s A. y e. t b e. ( x i y ) ) ) }
end
