
axiom df-homul
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- .op = ( f e. CC , g e. ( ~H ^m ~H ) |-> ( x e. ~H |-> ( f .h ( g ` x ) ) ) )
end
