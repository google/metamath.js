
axiom df-cllaw
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vo: setvar o
  assert |- clLaw = { <. o , m >. | A. x e. m A. y e. m ( x o y ) e. m }
end
