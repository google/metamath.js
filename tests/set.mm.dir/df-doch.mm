
axiom df-doch
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vk: setvar k
  assert |- ocH = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. ~P ( Base ` ( ( DVecH ` k ) ` w ) ) |-> ( ( ( DIsoH ` k ) ` w ) ` ( ( oc ` k ) ` ( ( glb ` k ) ` { y e. ( Base ` k ) | x C_ ( ( ( DIsoH ` k ) ` w ) ` y ) } ) ) ) ) ) )
end
