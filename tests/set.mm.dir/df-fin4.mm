
axiom df-fin4
  let vx: setvar x
  let vy: setvar y
  assert |- Fin4 = { x | -. E. y ( y C. x /\ y ~~ x ) }
end
