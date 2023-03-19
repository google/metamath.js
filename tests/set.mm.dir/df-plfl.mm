
axiom df-plfl
  let vz: setvar z
  let vt: setvar t
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- polyFld = ( r e. _V , p e. _V |-> [_ ( Poly1 ` r ) / s ]_ [_ ( ( RSpan ` s ) ` { p } ) / i ]_ [_ ( z e. ( Base ` r ) |-> [ ( z ( .s ` s ) ( 1r ` s ) ) ] ( s ~QG i ) ) / f ]_ <. [_ ( s /s ( s ~QG i ) ) / t ]_ ( ( t toNrmGrp ( iota_ n e. ( AbsVal ` t ) ( n o. f ) = ( norm ` r ) ) ) sSet <. ( le ` ndx ) , [_ ( z e. ( Base ` t ) |-> ( iota_ q e. z ( r deg1 q ) < ( r deg1 p ) ) ) / g ]_ ( `' g o. ( ( le ` s ) o. g ) ) >. ) , f >. )
end
