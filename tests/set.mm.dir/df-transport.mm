
axiom df-transport
  let vx: setvar x
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- TransportTo = { <. <. p , q >. , x >. | E. n e. NN ( ( p e. ( ( EE ` n ) X. ( EE ` n ) ) /\ q e. ( ( EE ` n ) X. ( EE ` n ) ) /\ ( 1st ` q ) =/= ( 2nd ` q ) ) /\ x = ( iota_ r e. ( EE ` n ) ( ( 2nd ` q ) Btwn <. ( 1st ` q ) , r >. /\ <. ( 2nd ` q ) , r >. Cgr p ) ) ) }
end
