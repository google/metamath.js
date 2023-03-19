
axiom df-le2
  let wva: term a
  let wvb: term b
  assume df-le2.1: |- a =< b
  assert |- ( a v b ) = b
end
