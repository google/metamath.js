
axiom df-or
  let vx: var x
  let vp: var p
  let vq: var q
  assert |- T. |= [ \/ = \ p : bool . \ q : bool . ( ! \ x : bool . [ [ p : bool ==> x : bool ] ==> [ [ q : bool ==> x : bool ] ==> x : bool ] ] ) ]
end
