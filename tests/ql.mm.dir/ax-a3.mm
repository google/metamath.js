
axiom ax-a3
  param wva: term a
  param wvb: term b
  param wvc: term c
  assert |- ( ( a v b ) v c ) = ( a v ( b v c ) )
end
