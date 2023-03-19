
axiom df-fin
  let vx: setvar x
  let vy: setvar y
  assert |- Fin = { x | E. y e. _om x ~~ y }
end
