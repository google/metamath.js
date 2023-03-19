
axiom df-fi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- fi = ( x e. _V |-> { z | E. y e. ( ~P x i^i Fin ) z = |^| y } )
end
