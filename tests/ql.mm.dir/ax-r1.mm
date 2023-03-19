
axiom ax-r1
  let wva: term a
  let wvb: term b
  assume r1.1: |- a = b
  assert |- b = a
end
