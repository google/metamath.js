
axiom ax-4oa
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assert |- ( ( a ->1 d ) ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) =< ( b ->1 d )
end
