
axiom df-f11
  let hal: type al
  let hbe: type be
  let vx: var x
  let vy: var y
  let vf: var f
  assert |- T. |= [ 1-1 = \ f : ( al -> be ) . ( ! \ x : al . ( ! \ y : al . [ [ ( f : ( al -> be ) x : al ) = ( f : ( al -> be ) y : al ) ] ==> [ x : al = y : al ] ] ) ) ]
end
