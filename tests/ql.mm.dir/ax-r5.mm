
axiom ax-r5
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume r5.1: |- a = b
  assert |- ( a v c ) = ( b v c )
end
