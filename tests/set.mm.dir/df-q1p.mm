
axiom df-q1p
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vb: setvar b
  assert |- quot1p = ( r e. _V |-> [_ ( Poly1 ` r ) / p ]_ [_ ( Base ` p ) / b ]_ ( f e. b , g e. b |-> ( iota_ q e. b ( ( deg1 ` r ) ` ( f ( -g ` p ) ( q ( .r ` p ) g ) ) ) < ( ( deg1 ` r ) ` g ) ) ) )
end
