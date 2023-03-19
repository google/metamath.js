
axiom df-fo
  param hal: type al
  param hbe: type be
  param vx: var x
  param vy: var y
  param vf: var f
  assert |- T. |= [ onto = \ f : ( al -> be ) . ( ! \ y : be . ( ? \ x : al . [ y : be = ( f : ( al -> be ) x : al ) ] ) ) ]
end
