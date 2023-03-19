
axiom df-b3
  param wva: term a
  param wvb: term b
  assert |- ( a <->3 b ) = ( ( a ->3 b ) ^ ( b ->3 a ) )
end
