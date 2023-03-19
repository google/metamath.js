
axiom df-docaN
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vk: setvar k
  assert |- ocA = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. ~P ( ( LTrn ` k ) ` w ) |-> ( ( ( DIsoA ` k ) ` w ) ` ( ( ( ( oc ` k ) ` ( `' ( ( DIsoA ` k ) ` w ) ` |^| { z e. ran ( ( DIsoA ` k ) ` w ) | x C_ z } ) ) ( join ` k ) ( ( oc ` k ) ` w ) ) ( meet ` k ) w ) ) ) ) )
end
