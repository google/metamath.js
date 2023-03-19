
axiom df-lplanes
  let vx: setvar x
  let vk: setvar k
  let vp: setvar p
  assert |- LPlanes = ( k e. _V |-> { x e. ( Base ` k ) | E. p e. ( LLines ` k ) p ( <o ` k ) x } )
end
