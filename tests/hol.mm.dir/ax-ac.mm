
axiom ax-ac
  let hal: type al
  let vx: var x
  let vp: var p
  assert |- T. |= ( ! \ p : ( al -> bool ) . ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==> ( p : ( al -> bool ) ( @ p : ( al -> bool ) ) ) ] ) )
end
