
axiom df-icc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- [,] = ( x e. RR* , y e. RR* |-> { z e. RR* | ( x <_ z /\ z <_ y ) } )
end
