
axiom df-tanh
  let vx: setvar x
  assert |- tanh = ( x e. ( `' cosh " ( CC \ { 0 } ) ) |-> ( ( tan ` ( _i x. x ) ) / _i ) )
end
