
axiom df-ldil
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assert |- LDil = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { f e. ( LAut ` k ) | A. x e. ( Base ` k ) ( x ( le ` k ) w -> ( f ` x ) = x ) } ) )
end
