
axiom df-hnorm
  let vx: setvar x
  assert |- normh = ( x e. dom dom .ih |-> ( sqrt ` ( x .ih x ) ) )
end
