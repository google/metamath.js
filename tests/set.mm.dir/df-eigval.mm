
axiom df-eigval
  let vx: setvar x
  let vt: setvar t
  assert |- eigval = ( t e. ( ~H ^m ~H ) |-> ( x e. ( eigvec ` t ) |-> ( ( ( t ` x ) .ih x ) / ( ( normh ` x ) ^ 2 ) ) ) )
end
