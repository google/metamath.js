
axiom ax-3oa
  param wva: term a
  param wvb: term b
  param wvc: term c
  assert |- ( ( a ->1 c ) ^ ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) =< ( b ->1 c )
end
