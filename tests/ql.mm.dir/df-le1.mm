
axiom df-le1
  param wva: term a
  param wvb: term b
  assume df-le1.1: |- ( a v b ) = b
  assert |- a =< b
end
