
axiom ax-eta
  let hal: type al
  let hbe: type be
  let vx: var x
  let vf: var f
  assert |- T. |= ( ! \ f : ( al -> be ) . [ \ x : al . ( f : ( al -> be ) x : al ) = f : ( al -> be ) ] )
end
