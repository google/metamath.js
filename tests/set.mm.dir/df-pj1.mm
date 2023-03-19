
axiom df-pj1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  assert |- proj1 = ( w e. _V |-> ( t e. ~P ( Base ` w ) , u e. ~P ( Base ` w ) |-> ( z e. ( t ( LSSum ` w ) u ) |-> ( iota_ x e. t E. y e. u z = ( x ( +g ` w ) y ) ) ) ) )
end
