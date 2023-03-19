

axiom ax-cb2
  param ta: term A
  param tr: term R
  assume ax-cb.1: |- R |= A
  assert |- A : bool
end
