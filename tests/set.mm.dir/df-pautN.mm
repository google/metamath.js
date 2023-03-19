
axiom df-pautN
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vk: setvar k
  assert |- PAut = ( k e. _V |-> { f | ( f : ( PSubSp ` k ) -1-1-onto-> ( PSubSp ` k ) /\ A. x e. ( PSubSp ` k ) A. y e. ( PSubSp ` k ) ( x C_ y <-> ( f ` x ) C_ ( f ` y ) ) ) } )
end
