
axiom df-id4oa
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assert |- ( a == c , d ==OA b ) = ( ( a == d ==OA b ) v ( ( a == d ==OA c ) ^ ( b == d ==OA c ) ) )
end
