
axiom df-spec
  let vx: setvar x
  let vt: setvar t
  assert |- Lambda = ( t e. ( ~H ^m ~H ) |-> { x e. CC | -. ( t -op ( x .op ( _I |` ~H ) ) ) : ~H -1-1-> ~H } )
end
