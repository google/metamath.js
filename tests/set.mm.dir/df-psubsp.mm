
axiom df-psubsp
  let vk: setvar k
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- PSubSp = ( k e. _V |-> { s | ( s C_ ( Atoms ` k ) /\ A. p e. s A. q e. s A. r e. ( Atoms ` k ) ( r ( le ` k ) ( p ( join ` k ) q ) -> r e. s ) ) } )
end
