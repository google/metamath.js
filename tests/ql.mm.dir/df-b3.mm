
axiom df-b3
  let wva: term a
  let wvb: term b
  assert |- ( a <->3 b ) = ( ( a ->3 b ) ^ ( b ->3 a ) )
end
