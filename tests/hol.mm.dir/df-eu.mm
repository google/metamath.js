
axiom df-eu
  let hal: type al
  let vx: var x
  let vy: var y
  let vp: var p
  assert |- T. |= [ ?! = \ p : ( al -> bool ) . ( ? \ y : al . ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) = [ x : al = y : al ] ] ) ) ]
end
