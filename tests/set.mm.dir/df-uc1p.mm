
axiom df-uc1p
  let vf: setvar f
  let vr: setvar r
  assert |- Unic1p = ( r e. _V |-> { f e. ( Base ` ( Poly1 ` r ) ) | ( f =/= ( 0g ` ( Poly1 ` r ) ) /\ ( ( coe1 ` f ) ` ( ( deg1 ` r ) ` f ) ) e. ( Unit ` r ) ) } )
end
