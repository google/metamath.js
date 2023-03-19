
axiom df-atan
  let vx: setvar x
  assert |- arctan = ( x e. ( CC \ { -u _i , _i } ) |-> ( ( _i / 2 ) x. ( ( log ` ( 1 - ( _i x. x ) ) ) - ( log ` ( 1 + ( _i x. x ) ) ) ) ) )
end
