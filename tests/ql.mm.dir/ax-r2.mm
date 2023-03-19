
axiom ax-r2
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume r2.1: |- a = b
  assume r2.2: |- b = c
  assert |- a = c
end
