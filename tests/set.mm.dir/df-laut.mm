
axiom df-laut
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vk: setvar k
  assert |- LAut = ( k e. _V |-> { f | ( f : ( Base ` k ) -1-1-onto-> ( Base ` k ) /\ A. x e. ( Base ` k ) A. y e. ( Base ` k ) ( x ( le ` k ) y <-> ( f ` x ) ( le ` k ) ( f ` y ) ) ) } )
end
