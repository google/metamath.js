
axiom ax-ml
  param wva: term a
  param wvb: term b
  param wvc: term c
  assert |- ( ( a v b ) ^ ( a v c ) ) =< ( a v ( b ^ ( a v c ) ) )
end
