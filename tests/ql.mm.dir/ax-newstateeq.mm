
axiom ax-newstateeq
  param wva: term a
  param wvb: term b
  param wvc: term c
  assert |- ( ( ( a ->1 b ) ->1 ( c ->1 b ) ) ^ ( ( a ->1 c ) ^ ( b ->1 a ) ) ) =< ( c ->1 a )
end
