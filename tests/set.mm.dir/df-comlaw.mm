
axiom df-comlaw
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vo: setvar o
  assert |- comLaw = { <. o , m >. | A. x e. m A. y e. m ( x o y ) = ( y o x ) }
end
