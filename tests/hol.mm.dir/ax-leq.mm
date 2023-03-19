
axiom ax-leq
  let hal: type al
  let hbe: type be
  let vx: var x
  let ta: term A
  let tb: term B
  let tr: term R
  assume ax-leq.1: |- A : be
  assume ax-leq.2: |- B : be
  assume ax-leq.3: |- R |= ( ( = A ) B )
  assert |- R |= ( ( = \ x : al . A ) \ x : al . B )
end
