
axiom df-assa
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- AssAlg = { w e. ( LMod i^i Ring ) | [. ( Scalar ` w ) / f ]. ( f e. CRing /\ A. r e. ( Base ` f ) A. x e. ( Base ` w ) A. y e. ( Base ` w ) [. ( .s ` w ) / s ]. [. ( .r ` w ) / t ]. ( ( ( r s x ) t y ) = ( r s ( x t y ) ) /\ ( x t ( r s y ) ) = ( r s ( x t y ) ) ) ) }
end
