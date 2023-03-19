
axiom df-hodif
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- -op = ( f e. ( ~H ^m ~H ) , g e. ( ~H ^m ~H ) |-> ( x e. ~H |-> ( ( f ` x ) -h ( g ` x ) ) ) )
end
