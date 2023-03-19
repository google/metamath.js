
axiom df-disoa
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assert |- DIsoA = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. { y e. ( Base ` k ) | y ( le ` k ) w } |-> { f e. ( ( LTrn ` k ) ` w ) | ( ( ( trL ` k ) ` w ) ` f ) ( le ` k ) x } ) ) )
end
