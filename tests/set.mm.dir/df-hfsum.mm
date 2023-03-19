
axiom df-hfsum
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- +fn = ( f e. ( CC ^m ~H ) , g e. ( CC ^m ~H ) |-> ( x e. ~H |-> ( ( f ` x ) + ( g ` x ) ) ) )
end
