
axiom df-ltrn
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  let vq: setvar q
  let vp: setvar p
  assert |- LTrn = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { f e. ( ( LDil ` k ) ` w ) | A. p e. ( Atoms ` k ) A. q e. ( Atoms ` k ) ( ( -. p ( le ` k ) w /\ -. q ( le ` k ) w ) -> ( ( p ( join ` k ) ( f ` p ) ) ( meet ` k ) w ) = ( ( q ( join ` k ) ( f ` q ) ) ( meet ` k ) w ) ) } ) )
end
