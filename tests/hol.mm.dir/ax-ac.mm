
axiom ax-ac
  param hal: type al
  param vx: var x
  param vp: var p
  assert |- T. |= ( ! \ p : ( al -> bool ) . ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==> ( p : ( al -> bool ) ( @ p : ( al -> bool ) ) ) ] ) )
end
