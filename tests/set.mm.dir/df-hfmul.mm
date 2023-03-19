
axiom df-hfmul
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assert |- .fn = ( f e. CC , g e. ( CC ^m ~H ) |-> ( x e. ~H |-> ( f x. ( g ` x ) ) ) )
end
