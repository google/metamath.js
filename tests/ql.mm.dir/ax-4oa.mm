
axiom ax-4oa
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assert |- ( ( a ->1 d ) ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) =< ( b ->1 d )
end
