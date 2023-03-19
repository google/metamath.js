
axiom ax-r1
  param wva: term a
  param wvb: term b
  assume r1.1: |- a = b
  assert |- b = a
end
