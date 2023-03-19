
axiom df-i4
  let wva: term a
  let wvb: term b
  assert |- ( a ->4 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v ( ( a ' v b ) ^ b ' ) )
end
