
axiom df-b
  param wva: term a
  param wvb: term b
  assert |- ( a == b ) = ( ( a ' v b ' ) ' v ( a v b ) ' )
end
