
axiom df-djaN
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vk: setvar k
  assert |- vA = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. ~P ( ( LTrn ` k ) ` w ) , y e. ~P ( ( LTrn ` k ) ` w ) |-> ( ( ( ocA ` k ) ` w ) ` ( ( ( ( ocA ` k ) ` w ) ` x ) i^i ( ( ( ocA ` k ) ` w ) ` y ) ) ) ) ) )
end
