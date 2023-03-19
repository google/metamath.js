
axiom df-acos
  let vx: setvar x
  assert |- arccos = ( x e. CC |-> ( ( _pi / 2 ) - ( arcsin ` x ) ) )
end
