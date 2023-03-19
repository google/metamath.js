
axiom df-dih
  let vx: setvar x
  let vw: setvar w
  let vu: setvar u
  let vk: setvar k
  let vq: setvar q
  assert |- DIsoH = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. ( Base ` k ) |-> if ( x ( le ` k ) w , ( ( ( DIsoB ` k ) ` w ) ` x ) , ( iota_ u e. ( LSubSp ` ( ( DVecH ` k ) ` w ) ) A. q e. ( Atoms ` k ) ( ( -. q ( le ` k ) w /\ ( q ( join ` k ) ( x ( meet ` k ) w ) ) = x ) -> u = ( ( ( ( DIsoC ` k ) ` w ) ` q ) ( LSSum ` ( ( DVecH ` k ) ` w ) ) ( ( ( DIsoB ` k ) ` w ) ` ( x ( meet ` k ) w ) ) ) ) ) ) ) ) )
end
