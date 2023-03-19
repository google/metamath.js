
axiom df-mbf
  let vx: setvar x
  let vf: setvar f
  assert |- MblFn = { f e. ( CC ^pm RR ) | A. x e. ran (,) ( ( `' ( Re o. f ) " x ) e. dom vol /\ ( `' ( Im o. f ) " x ) e. dom vol ) }
end
