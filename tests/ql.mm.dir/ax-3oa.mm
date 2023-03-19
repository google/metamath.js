
axiom ax-3oa
  let wva: term a
  let wvb: term b
  let wvc: term c
  assert |- ( ( a ->1 c ) ^ ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) =< ( b ->1 c )
end
