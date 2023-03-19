
axiom df-tendo
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assert |- TEndo = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { f | ( f : ( ( LTrn ` k ) ` w ) --> ( ( LTrn ` k ) ` w ) /\ A. x e. ( ( LTrn ` k ) ` w ) A. y e. ( ( LTrn ` k ) ` w ) ( f ` ( x o. y ) ) = ( ( f ` x ) o. ( f ` y ) ) /\ A. x e. ( ( LTrn ` k ) ` w ) ( ( ( trL ` k ) ` w ) ` ( f ` x ) ) ( le ` k ) ( ( ( trL ` k ) ` w ) ` x ) ) } ) )
end
