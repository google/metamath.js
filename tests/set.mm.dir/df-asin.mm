
axiom df-asin
  let vx: setvar x
  assert |- arcsin = ( x e. CC |-> ( -u _i x. ( log ` ( ( _i x. x ) + ( sqrt ` ( 1 - ( x ^ 2 ) ) ) ) ) ) )
end
