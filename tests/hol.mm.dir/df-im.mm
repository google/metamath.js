
axiom df-im
  param vp: var p
  param vq: var q
  assert |- T. |= [ ==> = \ p : bool . \ q : bool . [ [ p : bool /\ q : bool ] = p : bool ] ]
end
