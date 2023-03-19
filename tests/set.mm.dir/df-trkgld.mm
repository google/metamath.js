
axiom df-trkgld
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vp: setvar p
  let vd: setvar d
  assert |- TarskiGDim>= = { <. g , n >. | [. ( Base ` g ) / p ]. [. ( dist ` g ) / d ]. [. ( Itv ` g ) / i ]. E. f ( f : ( 1 ..^ n ) -1-1-> p /\ E. x e. p E. y e. p E. z e. p ( A. j e. ( 2 ..^ n ) ( ( ( f ` 1 ) d x ) = ( ( f ` j ) d x ) /\ ( ( f ` 1 ) d y ) = ( ( f ` j ) d y ) /\ ( ( f ` 1 ) d z ) = ( ( f ` j ) d z ) ) /\ -. ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) ) ) ) }
end
