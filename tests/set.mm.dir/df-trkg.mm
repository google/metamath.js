
axiom df-trkg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  assert |- TarskiG = ( ( TarskiGC i^i TarskiGB ) i^i ( TarskiGCB i^i { f | [. ( Base ` f ) / p ]. [. ( Itv ` f ) / i ]. ( LineG ` f ) = ( x e. p , y e. ( p \ { x } ) |-> { z e. p | ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) ) } ) } ) )
end
