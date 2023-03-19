
axiom ax-distrl
  let hal: type al
  let hbe: type be
  let hga: type ga
  let vx: var x
  let vy: var y
  let ta: term A
  let tb: term B
  assume ax-distrl.1: |- A : ga
  assume ax-distrl.2: |- B : al
  assert |- T. |= ( ( = ( \ x : al . \ y : be . A B ) ) \ y : be . ( \ x : al . A B ) )
end
