
axiom df-ring
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vf: setvar f
  let vr: setvar r
  let vp: setvar p
  assert |- Ring = { f e. Grp | ( ( mulGrp ` f ) e. Mnd /\ [. ( Base ` f ) / r ]. [. ( +g ` f ) / p ]. [. ( .r ` f ) / t ]. A. x e. r A. y e. r A. z e. r ( ( x t ( y p z ) ) = ( ( x t y ) p ( x t z ) ) /\ ( ( x p y ) t z ) = ( ( x t z ) p ( y t z ) ) ) ) }
end
