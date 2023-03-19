
axiom df-oms
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vr: setvar r
  let va: setvar a
  assert |- toOMeas = ( r e. _V |-> ( a e. ~P U. dom r |-> inf ( ran ( x e. { z e. ~P dom r | ( a C_ U. z /\ z ~<_ _om ) } |-> sum* y e. x ( r ` y ) ) , ( 0 [,] +oo ) , < ) ) )
end
