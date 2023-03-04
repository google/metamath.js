

axiom ax-cb1
  let ta: term A
  let tr: term R
  assume ax-cb.1: |- R |= A
  assert |- R : bool
end
