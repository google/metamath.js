
axiom df-i5
  let wva: term a
  let wvb: term b
  assert |- ( a ->5 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v ( a ' ^ b ' ) )
end
