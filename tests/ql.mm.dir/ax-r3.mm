
axiom ax-r3
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume r3.1: |- ( c v c ' ) = ( ( a ' v b ' ) ' v ( a v b ) ' )
  assert |- a = b
end
