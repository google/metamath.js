
axiom df-lsm
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  assert |- LSSum = ( w e. _V |-> ( t e. ~P ( Base ` w ) , u e. ~P ( Base ` w ) |-> ran ( x e. t , y e. u |-> ( x ( +g ` w ) y ) ) ) )
end
