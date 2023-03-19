
axiom df-or
  param vx: var x
  param vp: var p
  param vq: var q
  assert |- T. |= [ \/ = \ p : bool . \ q : bool . ( ! \ x : bool . [ [ p : bool ==> x : bool ] ==> [ [ q : bool ==> x : bool ] ==> x : bool ] ] ) ]
end
