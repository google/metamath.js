
axiom df-sigagen
  let vx: setvar x
  let vs: setvar s
  assert |- sigaGen = ( x e. _V |-> |^| { s e. ( sigAlgebra ` U. x ) | x C_ s } )
end
