
axiom df-im
  let vp: var p
  let vq: var q
  assert |- T. |= [ ==> = \ p : bool . \ q : bool . [ [ p : bool /\ q : bool ] = p : bool ] ]
end
