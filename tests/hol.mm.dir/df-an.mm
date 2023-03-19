
axiom df-an
  let vf: var f
  let vp: var p
  let vq: var q
  assert |- T. |= [ /\ = \ p : bool . \ q : bool . [ \ f : ( bool -> ( bool -> bool ) ) . [ p : bool f : ( bool -> ( bool -> bool ) ) q : bool ] = \ f : ( bool -> ( bool -> bool ) ) . [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ]
end
