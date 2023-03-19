
axiom df-id3oa
  param wva: term a
  param wvb: term b
  param wvc: term c
  assert |- ( a == c ==OA b ) = ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) )
end
