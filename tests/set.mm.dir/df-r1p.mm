
axiom df-r1p
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vb: setvar b
  assert |- rem1p = ( r e. _V |-> [_ ( Base ` ( Poly1 ` r ) ) / b ]_ ( f e. b , g e. b |-> ( f ( -g ` ( Poly1 ` r ) ) ( ( f ( quot1p ` r ) g ) ( .r ` ( Poly1 ` r ) ) g ) ) ) )
end
