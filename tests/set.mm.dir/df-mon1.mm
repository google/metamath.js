
axiom df-mon1
  let vf: setvar f
  let vr: setvar r
  assert |- Monic1p = ( r e. _V |-> { f e. ( Base ` ( Poly1 ` r ) ) | ( f =/= ( 0g ` ( Poly1 ` r ) ) /\ ( ( coe1 ` f ) ` ( ( deg1 ` r ) ` f ) ) = ( 1r ` r ) ) } )
end
