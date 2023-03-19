

axiom df-al
  param hal: type al
  param vx: var x
  param vp: var p
  assert |- T. |= [ ! = \ p : ( al -> bool ) . [ p : ( al -> bool ) = \ x : al . T. ] ]
end
