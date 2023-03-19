
axiom df-rng0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vf: setvar f
  let vp: setvar p
  let vb: setvar b
  assert |- Rng = { f e. Abel | ( ( mulGrp ` f ) e. SGrp /\ [. ( Base ` f ) / b ]. [. ( +g ` f ) / p ]. [. ( .r ` f ) / t ]. A. x e. b A. y e. b A. z e. b ( ( x t ( y p z ) ) = ( ( x t y ) p ( x t z ) ) /\ ( ( x p y ) t z ) = ( ( x t z ) p ( y t z ) ) ) ) }
end
