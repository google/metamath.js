
axiom df-staf
  let vx: setvar x
  let vf: setvar f
  assert |- *rf = ( f e. _V |-> ( x e. ( Base ` f ) |-> ( ( *r ` f ) ` x ) ) )
end
