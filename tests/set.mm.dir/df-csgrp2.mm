
axiom df-csgrp2
  let vg: setvar g
  assert |- CSGrpALT = { g e. SGrpALT | ( +g ` g ) comLaw ( Base ` g ) }
end
