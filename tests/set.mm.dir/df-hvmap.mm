
axiom df-hvmap
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let vj: setvar j
  let vk: setvar k
  assert |- HVMap = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. ( ( Base ` ( ( DVecH ` k ) ` w ) ) \ { ( 0g ` ( ( DVecH ` k ) ` w ) ) } ) |-> ( v e. ( Base ` ( ( DVecH ` k ) ` w ) ) |-> ( iota_ j e. ( Base ` ( Scalar ` ( ( DVecH ` k ) ` w ) ) ) E. t e. ( ( ( ocH ` k ) ` w ) ` { x } ) v = ( t ( +g ` ( ( DVecH ` k ) ` w ) ) ( j ( .s ` ( ( DVecH ` k ) ` w ) ) x ) ) ) ) ) ) )
end
