
axiom df-lhyp
  let vx: setvar x
  let vk: setvar k
  assert |- LHyp = ( k e. _V |-> { x e. ( Base ` k ) | x ( <o ` k ) ( 1. ` k ) } )
end
