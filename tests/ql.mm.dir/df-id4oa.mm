
axiom df-id4oa
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assert |- ( a == c , d ==OA b ) = ( ( a == d ==OA b ) v ( ( a == d ==OA c ) ^ ( b == d ==OA c ) ) )
end
