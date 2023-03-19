
axiom df-eqg
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vr: setvar r
  assert |- ~QG = ( r e. _V , i e. _V |-> { <. x , y >. | ( { x , y } C_ ( Base ` r ) /\ ( ( ( invg ` r ) ` x ) ( +g ` r ) y ) e. i ) } )
end
