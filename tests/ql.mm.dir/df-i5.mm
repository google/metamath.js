
axiom df-i5
  param wva: term a
  param wvb: term b
  assert |- ( a ->5 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v ( a ' ^ b ' ) )
end
