
axiom df-cph
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assert |- CPreHil = { w e. ( PreHil i^i NrmMod ) | [. ( Scalar ` w ) / f ]. [. ( Base ` f ) / k ]. ( f = ( CCfld |`s k ) /\ ( sqrt " ( k i^i ( 0 [,) +oo ) ) ) C_ k /\ ( norm ` w ) = ( x e. ( Base ` w ) |-> ( sqrt ` ( x ( .i ` w ) x ) ) ) ) }
end
