
axiom df-an
  param vf: var f
  param vp: var p
  param vq: var q
  assert |- T. |= [ /\ = \ p : bool . \ q : bool . [ \ f : ( bool -> ( bool -> bool ) ) . [ p : bool f : ( bool -> ( bool -> bool ) ) q : bool ] = \ f : ( bool -> ( bool -> bool ) ) . [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ]
end
