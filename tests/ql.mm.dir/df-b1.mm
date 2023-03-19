
axiom df-b1
  let wva: term a
  let wvb: term b
  assert |- ( a <->1 b ) = ( ( a ->1 b ) ^ ( b ->1 a ) )
end
