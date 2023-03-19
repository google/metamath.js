
axiom df-lines
  let vk: setvar k
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- Lines = ( k e. _V |-> { s | E. q e. ( Atoms ` k ) E. r e. ( Atoms ` k ) ( q =/= r /\ s = { p e. ( Atoms ` k ) | p ( le ` k ) ( q ( join ` k ) r ) } ) } )
end
