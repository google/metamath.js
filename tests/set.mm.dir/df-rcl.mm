
axiom df-rcl
  let vx: setvar x
  let vz: setvar z
  assert |- r* = ( x e. _V |-> |^| { z | ( x C_ z /\ ( _I |` ( dom z u. ran z ) ) C_ z ) } )
end
