

axiom ax-17
  param hal: type al
  param hbe: type be
  param vx: var x
  param ta: term A
  param tb: term B
  assume ax-17.1: |- A : be
  assume ax-17.2: |- B : al
  assert |- T. |= [ ( \ x : al . A B ) = A ]
end
