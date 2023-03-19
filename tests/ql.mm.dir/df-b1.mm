
axiom df-b1
  param wva: term a
  param wvb: term b
  assert |- ( a <->1 b ) = ( ( a ->1 b ) ^ ( b ->1 a ) )
end
