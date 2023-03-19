
axiom df-id3
  param wva: term a
  param wvb: term b
  assert |- ( a ==3 b ) = ( ( a ' v b ) ^ ( a v ( a ' ^ b ' ) ) )
end
