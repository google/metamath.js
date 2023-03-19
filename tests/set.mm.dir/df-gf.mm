
axiom df-gf
  let vx: setvar x
  let vn: setvar n
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  assert |- GF = ( p e. Prime , n e. NN |-> [_ ( Z/nZ ` p ) / r ]_ ( 1st ` ( r splitFld { [_ ( Poly1 ` r ) / s ]_ [_ ( var1 ` r ) / x ]_ ( ( ( p ^ n ) ( .g ` ( mulGrp ` s ) ) x ) ( -g ` s ) x ) } ) ) )
end
