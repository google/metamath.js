
axiom df-eu
  param hal: type al
  param vx: var x
  param vy: var y
  param vp: var p
  assert |- T. |= [ ?! = \ p : ( al -> bool ) . ( ? \ y : al . ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) = [ x : al = y : al ] ] ) ) ]
end
