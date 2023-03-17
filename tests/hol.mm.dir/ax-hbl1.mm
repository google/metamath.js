

axiom ax-hbl1
  let hal: type al
  let hbe: type be
  let hga: type ga
  let vx: var x
  let ta: term A
  let tb: term B
  assume ax-hbl1.1: |- A : ga
  assume ax-hbl1.2: |- B : al
  assert |- T. |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ]
end
