
axiom df-id4
  param wva: term a
  param wvb: term b
  assert |- ( a ==4 b ) = ( ( a ' v b ) ^ ( b ' v ( a ^ b ) ) )
end
