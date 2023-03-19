
axiom df-fin5
  let vx: setvar x
  assert |- Fin5 = { x | ( x = (/) \/ x ~< ( x +c x ) ) }
end
