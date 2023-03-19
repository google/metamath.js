
axiom df-rtrcl
  let vx: setvar x
  let vz: setvar z
  assert |- t* = ( x e. _V |-> |^| { z | ( ( _I |` ( dom x u. ran x ) ) C_ z /\ x C_ z /\ ( z o. z ) C_ z ) } )
end
