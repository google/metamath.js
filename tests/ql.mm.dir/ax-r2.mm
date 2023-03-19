
axiom ax-r2
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume r2.1: |- a = b
  assume r2.2: |- b = c
  assert |- a = c
end
