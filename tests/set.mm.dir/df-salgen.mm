
axiom df-salgen
  let vx: setvar x
  let vs: setvar s
  assert |- SalGen = ( x e. _V |-> |^| { s e. SAlg | ( U. s = U. x /\ x C_ s ) } )
end
