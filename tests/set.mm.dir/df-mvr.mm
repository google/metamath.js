
axiom df-mvr
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vr: setvar r
  assert |- mVar = ( i e. _V , r e. _V |-> ( x e. i |-> ( f e. { h e. ( NN0 ^m i ) | ( `' h " NN ) e. Fin } |-> if ( f = ( y e. i |-> if ( y = x , 1 , 0 ) ) , ( 1r ` r ) , ( 0g ` r ) ) ) ) )
end
