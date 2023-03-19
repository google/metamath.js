
axiom df-llines
  let vx: setvar x
  let vk: setvar k
  let vp: setvar p
  assert |- LLines = ( k e. _V |-> { x e. ( Base ` k ) | E. p e. ( Atoms ` k ) p ( <o ` k ) x } )
end
