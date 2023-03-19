
axiom df-trl
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  let vp: setvar p
  assert |- trL = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( f e. ( ( LTrn ` k ) ` w ) |-> ( iota_ x e. ( Base ` k ) A. p e. ( Atoms ` k ) ( -. p ( le ` k ) w -> x = ( ( p ( join ` k ) ( f ` p ) ) ( meet ` k ) w ) ) ) ) ) )
end
