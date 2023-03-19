
axiom df-fin6
  let vx: setvar x
  assert |- Fin6 = { x | ( x ~< 2o \/ x ~< ( x X. x ) ) }
end
