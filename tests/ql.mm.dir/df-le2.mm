
axiom df-le2
  param wva: term a
  param wvb: term b
  assume df-le2.1: |- a =< b
  assert |- ( a v b ) = b
end
