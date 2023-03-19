
axiom df-sgrp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let vo: setvar o
  let vb: setvar b
  assert |- SGrp = { g e. Mgm | [. ( Base ` g ) / b ]. [. ( +g ` g ) / o ]. A. x e. b A. y e. b A. z e. b ( ( x o y ) o z ) = ( x o ( y o z ) ) }
end
