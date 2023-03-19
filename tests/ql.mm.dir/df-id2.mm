
axiom df-id2
  let wva: term a
  let wvb: term b
  assert |- ( a ==2 b ) = ( ( a v b ' ) ^ ( b v ( a ' ^ b ' ) ) )
end
