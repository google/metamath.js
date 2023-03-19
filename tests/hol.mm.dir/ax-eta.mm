
axiom ax-eta
  param hal: type al
  param hbe: type be
  param vx: var x
  param vf: var f
  assert |- T. |= ( ! \ f : ( al -> be ) . [ \ x : al . ( f : ( al -> be ) x : al ) = f : ( al -> be ) ] )
end
