
axiom ax-cb2
  let ta: term A
  let tr: term R
  assume ax-cb.1: |- R |= A
  assert |- A : bool
end
