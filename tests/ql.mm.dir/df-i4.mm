
axiom df-i4
  param wva: term a
  param wvb: term b
  assert |- ( a ->4 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v ( ( a ' v b ) ^ b ' ) )
end
