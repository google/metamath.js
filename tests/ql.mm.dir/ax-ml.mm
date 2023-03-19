
axiom ax-ml
  let wva: term a
  let wvb: term b
  let wvc: term c
  assert |- ( ( a v b ) ^ ( a v c ) ) =< ( a v ( b ^ ( a v c ) ) )
end
