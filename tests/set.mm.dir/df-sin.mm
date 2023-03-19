
axiom df-sin
  let vx: setvar x
  assert |- sin = ( x e. CC |-> ( ( ( exp ` ( _i x. x ) ) - ( exp ` ( -u _i x. x ) ) ) / ( 2 x. _i ) ) )
end
