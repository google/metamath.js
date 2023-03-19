
axiom df-eigvec
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  assert |- eigvec = ( t e. ( ~H ^m ~H ) |-> { x e. ( ~H \ 0H ) | E. z e. CC ( t ` x ) = ( z .h x ) } )
end
