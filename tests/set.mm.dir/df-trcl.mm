
axiom df-trcl
  let vx: setvar x
  let vz: setvar z
  assert |- t+ = ( x e. _V |-> |^| { z | ( x C_ z /\ ( z o. z ) C_ z ) } )
end
