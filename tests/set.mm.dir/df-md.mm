
axiom df-md
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- MH = { <. x , y >. | ( ( x e. CH /\ y e. CH ) /\ A. z e. CH ( z C_ y -> ( ( z vH x ) i^i y ) = ( z vH ( x i^i y ) ) ) ) }
end
