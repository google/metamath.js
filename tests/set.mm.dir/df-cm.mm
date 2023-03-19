
axiom df-cm
  let vx: setvar x
  let vy: setvar y
  assert |- C_H = { <. x , y >. | ( ( x e. CH /\ y e. CH ) /\ x = ( ( x i^i y ) vH ( x i^i ( _|_ ` y ) ) ) ) }
end
