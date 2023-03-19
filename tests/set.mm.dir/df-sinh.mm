
axiom df-sinh
  let vx: setvar x
  assert |- sinh = ( x e. CC |-> ( ( sin ` ( _i x. x ) ) / _i ) )
end
