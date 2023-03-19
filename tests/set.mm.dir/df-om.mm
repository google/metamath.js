
axiom df-om
  let vx: setvar x
  let vy: setvar y
  assert |- _om = { x e. On | A. y ( Lim y -> x e. y ) }
end
