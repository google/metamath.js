
axiom df-trkgc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vp: setvar p
  let vd: setvar d
  assert |- TarskiGC = { f | [. ( Base ` f ) / p ]. [. ( dist ` f ) / d ]. ( A. x e. p A. y e. p ( x d y ) = ( y d x ) /\ A. x e. p A. y e. p A. z e. p ( ( x d y ) = ( z d z ) -> x = y ) ) }
end
