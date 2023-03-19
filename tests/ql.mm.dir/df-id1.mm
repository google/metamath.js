
axiom df-id1
  param wva: term a
  param wvb: term b
  assert |- ( a ==1 b ) = ( ( a v b ' ) ^ ( a ' v ( a ^ b ) ) )
end
