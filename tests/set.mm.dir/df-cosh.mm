
axiom df-cosh
  let vx: setvar x
  assert |- cosh = ( x e. CC |-> ( cos ` ( _i x. x ) ) )
end
