
axiom df-tgrp
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  assert |- TGrp = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { <. ( Base ` ndx ) , ( ( LTrn ` k ) ` w ) >. , <. ( +g ` ndx ) , ( f e. ( ( LTrn ` k ) ` w ) , g e. ( ( LTrn ` k ) ` w ) |-> ( f o. g ) ) >. } ) )
end
