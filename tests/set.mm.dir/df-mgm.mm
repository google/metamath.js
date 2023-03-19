
axiom df-mgm
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vo: setvar o
  let vb: setvar b
  assert |- Mgm = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / o ]. A. x e. b A. y e. b ( x o y ) e. b }
end
