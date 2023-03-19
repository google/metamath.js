
axiom ax-a3
  let wva: term a
  let wvb: term b
  let wvc: term c
  assert |- ( ( a v b ) v c ) = ( a v ( b v c ) )
end
