
axiom df-hdmap1
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vh: setvar h
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  assert |- HDMap1 = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { a | [. ( ( DVecH ` k ) ` w ) / u ]. [. ( Base ` u ) / v ]. [. ( LSpan ` u ) / n ]. [. ( ( LCDual ` k ) ` w ) / c ]. [. ( Base ` c ) / d ]. [. ( LSpan ` c ) / j ]. [. ( ( mapd ` k ) ` w ) / m ]. a e. ( x e. ( ( v X. d ) X. v ) |-> if ( ( 2nd ` x ) = ( 0g ` u ) , ( 0g ` c ) , ( iota_ h e. d ( ( m ` ( n ` { ( 2nd ` x ) } ) ) = ( j ` { h } ) /\ ( m ` ( n ` { ( ( 1st ` ( 1st ` x ) ) ( -g ` u ) ( 2nd ` x ) ) } ) ) = ( j ` { ( ( 2nd ` ( 1st ` x ) ) ( -g ` c ) h ) } ) ) ) ) ) } ) )
end
