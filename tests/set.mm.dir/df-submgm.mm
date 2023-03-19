
axiom df-submgm
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vs: setvar s
  assert |- SubMgm = ( s e. Mgm |-> { t e. ~P ( Base ` s ) | A. x e. t A. y e. t ( x ( +g ` s ) y ) e. t } )
end
