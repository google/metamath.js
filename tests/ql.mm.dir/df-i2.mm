
axiom df-i2
  param wva: term a
  param wvb: term b
  assert |- ( a ->2 b ) = ( b v ( a ' ^ b ' ) )
end
