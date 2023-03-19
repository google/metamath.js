
axiom df-srg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vf: setvar f
  let vn: setvar n
  let vr: setvar r
  let vp: setvar p
  assert |- SRing = { f e. CMnd | ( ( mulGrp ` f ) e. Mnd /\ [. ( Base ` f ) / r ]. [. ( +g ` f ) / p ]. [. ( .r ` f ) / t ]. [. ( 0g ` f ) / n ]. A. x e. r ( A. y e. r A. z e. r ( ( x t ( y p z ) ) = ( ( x t y ) p ( x t z ) ) /\ ( ( x p y ) t z ) = ( ( x t z ) p ( y t z ) ) ) /\ ( ( n t x ) = n /\ ( x t n ) = n ) ) ) }
end
