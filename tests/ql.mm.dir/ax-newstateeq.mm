
axiom ax-newstateeq
  let wva: term a
  let wvb: term b
  let wvc: term c
  assert |- ( ( ( a ->1 b ) ->1 ( c ->1 b ) ) ^ ( ( a ->1 c ) ^ ( b ->1 a ) ) ) =< ( c ->1 a )
end
