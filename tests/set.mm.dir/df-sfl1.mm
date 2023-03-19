
axiom df-sfl1
  let vt: setvar t
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vm: setvar m
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  let vb: setvar b
  assert |- splitFld1 = ( r e. _V , j e. _V |-> ( p e. ( Poly1 ` r ) |-> ( rec ( ( s e. _V , f e. _V |-> [_ ( mPoly ` s ) / m ]_ [_ { g e. ( ( Monic1p ` s ) i^i ( Irred ` m ) ) | ( g ( ||r ` m ) ( p o. f ) /\ 1 < ( s deg1 g ) ) } / b ]_ if ( ( ( p o. f ) = ( 0g ` m ) \/ b = (/) ) , <. s , f >. , [_ ( glb ` b ) / h ]_ [_ ( s polyFld h ) / t ]_ <. ( 1st ` t ) , ( f o. ( 2nd ` t ) ) >. ) ) , j ) ` ( card ` ( 1 ... ( r deg1 p ) ) ) ) ) )
end
