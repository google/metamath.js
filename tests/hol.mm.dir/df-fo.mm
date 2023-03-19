
axiom df-fo
  let hal: type al
  let hbe: type be
  let vx: var x
  let vy: var y
  let vf: var f
  assert |- T. |= [ onto = \ f : ( al -> be ) . ( ! \ y : be . ( ? \ x : al . [ y : be = ( f : ( al -> be ) x : al ) ] ) ) ]
end
