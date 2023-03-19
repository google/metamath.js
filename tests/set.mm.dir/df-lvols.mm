
axiom df-lvols
  let vx: setvar x
  let vk: setvar k
  let vp: setvar p
  assert |- LVols = ( k e. _V |-> { x e. ( Base ` k ) | E. p e. ( LPlanes ` k ) p ( <o ` k ) x } )
end
