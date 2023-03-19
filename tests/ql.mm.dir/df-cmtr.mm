
axiom df-cmtr
  param wva: term a
  param wvb: term b
  assert |- C ( a , b ) = ( ( ( a ^ b ) v ( a ^ b ' ) ) v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )
end
