
axiom df-sgns
  let vx: setvar x
  let vr: setvar r
  assert |- sgns = ( r e. _V |-> ( x e. ( Base ` r ) |-> if ( x = ( 0g ` r ) , 0 , if ( ( 0g ` r ) ( lt ` r ) x , 1 , -u 1 ) ) ) )
end
