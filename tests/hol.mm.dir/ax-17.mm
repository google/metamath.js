
axiom ax-17
  let hal: type al
  let hbe: type be
  let vx: var x
  let ta: term A
  let tb: term B
  assume ax-17.1: |- A : be
  assume ax-17.2: |- B : al
  assert |- T. |= [ ( \ x : al . A B ) = A ]
end
