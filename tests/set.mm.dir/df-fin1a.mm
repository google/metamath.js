
axiom df-fin1a
  let vx: setvar x
  let vy: setvar y
  assert |- Fin1a = { x | A. y e. ~P x ( y e. Fin \/ ( x \ y ) e. Fin ) }
end
