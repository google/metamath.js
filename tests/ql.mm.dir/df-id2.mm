
axiom df-id2
  param wva: term a
  param wvb: term b
  assert |- ( a ==2 b ) = ( ( a v b ' ) ^ ( b v ( a ' ^ b ' ) ) )
end
