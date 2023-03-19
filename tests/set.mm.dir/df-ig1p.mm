
axiom df-ig1p
  let vg: setvar g
  let vi: setvar i
  let vr: setvar r
  assert |- idlGen1p = ( r e. _V |-> ( i e. ( LIdeal ` ( Poly1 ` r ) ) |-> if ( i = { ( 0g ` ( Poly1 ` r ) ) } , ( 0g ` ( Poly1 ` r ) ) , ( iota_ g e. ( i i^i ( Monic1p ` r ) ) ( ( deg1 ` r ) ` g ) = inf ( ( ( deg1 ` r ) " ( i \ { ( 0g ` ( Poly1 ` r ) ) } ) ) , RR , < ) ) ) ) )
end
