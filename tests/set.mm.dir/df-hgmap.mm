
axiom df-hgmap
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vk: setvar k
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  assert |- HGMap = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { a | [. ( ( DVecH ` k ) ` w ) / u ]. [. ( Base ` ( Scalar ` u ) ) / b ]. [. ( ( HDMap ` k ) ` w ) / m ]. a e. ( x e. b |-> ( iota_ y e. b A. v e. ( Base ` u ) ( m ` ( x ( .s ` u ) v ) ) = ( y ( .s ` ( ( LCDual ` k ) ` w ) ) ( m ` v ) ) ) ) } ) )
end
