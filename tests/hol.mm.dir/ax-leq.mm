

axiom ax-leq
  param hal: type al
  param hbe: type be
  param vx: var x
  param ta: term A
  param tb: term B
  param tr: term R
  assume ax-leq.1: |- A : be
  assume ax-leq.2: |- B : be
  assume ax-leq.3: |- R |= ( ( = A ) B )
  assert |- R |= ( ( = \ x : al . A ) \ x : al . B )
end
