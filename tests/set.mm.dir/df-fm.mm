
axiom df-fm
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vf: setvar f
  assert |- FilMap = ( x e. _V , f e. _V |-> ( y e. ( fBas ` dom f ) |-> ( x filGen ran ( t e. y |-> ( f " t ) ) ) ) )
end
