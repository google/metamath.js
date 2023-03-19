
axiom df-asslaw
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vo: setvar o
  assert |- assLaw = { <. o , m >. | A. x e. m A. y e. m A. z e. m ( ( x o y ) o z ) = ( x o ( y o z ) ) }
end
