

axiom ax-hbl1
  param hal: type al
  param hbe: type be
  param hga: type ga
  param vx: var x
  param ta: term A
  param tb: term B
  assume ax-hbl1.1: |- A : ga
  assume ax-hbl1.2: |- B : al
  assert |- T. |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ]
end
