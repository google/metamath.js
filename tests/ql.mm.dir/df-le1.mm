
axiom df-le1
  let wva: term a
  let wvb: term b
  assume df-le1.1: |- ( a v b ) = b
  assert |- a =< b
end
