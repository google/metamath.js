
axiom ax-r4
  param wva: term a
  param wvb: term b
  assume r4.1: |- a = b
  assert |- a ' = b '
end
