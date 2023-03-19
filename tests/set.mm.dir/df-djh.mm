
axiom df-djh
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vk: setvar k
  assert |- joinH = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( x e. ~P ( Base ` ( ( DVecH ` k ) ` w ) ) , y e. ~P ( Base ` ( ( DVecH ` k ) ` w ) ) |-> ( ( ( ocH ` k ) ` w ) ` ( ( ( ( ocH ` k ) ` w ) ` x ) i^i ( ( ( ocH ` k ) ` w ) ` y ) ) ) ) ) )
end
