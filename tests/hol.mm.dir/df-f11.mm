
axiom df-f11
  param hal: type al
  param hbe: type be
  param vx: var x
  param vy: var y
  param vf: var f
  assert |- T. |= [ 1-1 = \ f : ( al -> be ) . ( ! \ x : al . ( ! \ y : al . [ [ ( f : ( al -> be ) x : al ) = ( f : ( al -> be ) y : al ) ] ==> [ x : al = y : al ] ] ) ) ]
end
