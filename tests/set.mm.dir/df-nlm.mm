
axiom df-nlm
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vf: setvar f
  assert |- NrmMod = { w e. ( NrmGrp i^i LMod ) | [. ( Scalar ` w ) / f ]. ( f e. NrmRing /\ A. x e. ( Base ` f ) A. y e. ( Base ` w ) ( ( norm ` w ) ` ( x ( .s ` w ) y ) ) = ( ( ( norm ` f ) ` x ) x. ( ( norm ` w ) ` y ) ) ) }
end
