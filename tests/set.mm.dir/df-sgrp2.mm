
axiom df-sgrp2
  let vg: setvar g
  assert |- SGrpALT = { g e. MgmALT | ( +g ` g ) assLaw ( Base ` g ) }
end
