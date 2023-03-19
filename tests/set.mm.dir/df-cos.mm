
axiom df-cos
  let vx: setvar x
  assert |- cos = ( x e. CC |-> ( ( ( exp ` ( _i x. x ) ) + ( exp ` ( -u _i x. x ) ) ) / 2 ) )
end
