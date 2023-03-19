
axiom df-abv
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vr: setvar r
  assert |- AbsVal = ( r e. Ring |-> { f e. ( ( 0 [,) +oo ) ^m ( Base ` r ) ) | A. x e. ( Base ` r ) ( ( ( f ` x ) = 0 <-> x = ( 0g ` r ) ) /\ A. y e. ( Base ` r ) ( ( f ` ( x ( .r ` r ) y ) ) = ( ( f ` x ) x. ( f ` y ) ) /\ ( f ` ( x ( +g ` r ) y ) ) <_ ( ( f ` x ) + ( f ` y ) ) ) ) } )
end
