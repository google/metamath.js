
axiom ax-r3
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume r3.1: |- ( c v c ' ) = ( ( a ' v b ' ) ' v ( a v b ) ' )
  assert |- a = b
end
