
axiom df-gfoo
  let vx: setvar x
  let vn: setvar n
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  assert |- GF_oo = ( p e. Prime |-> [_ ( Z/nZ ` p ) / r ]_ ( r polySplitLim ( n e. NN |-> { [_ ( Poly1 ` r ) / s ]_ [_ ( var1 ` r ) / x ]_ ( ( ( p ^ n ) ( .g ` ( mulGrp ` s ) ) x ) ( -g ` s ) x ) } ) ) )
end
