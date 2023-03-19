

axiom ax-cb1
  param ta: term A
  param tr: term R
  assume ax-cb.1: |- R |= A
  assert |- R : bool
end
