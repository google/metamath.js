
axiom ax-distrl
  param hal: type al
  param hbe: type be
  param hga: type ga
  param vx: var x
  param vy: var y
  param ta: term A
  param tb: term B
  assume ax-distrl.1: |- A : ga
  assume ax-distrl.2: |- B : al
  assert |- T. |= ( ( = ( \ x : al . \ y : be . A B ) ) \ y : be . ( \ x : al . A B ) )
end
