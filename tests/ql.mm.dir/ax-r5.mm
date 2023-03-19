
axiom ax-r5
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume r5.1: |- a = b
  assert |- ( a v c ) = ( b v c )
end
