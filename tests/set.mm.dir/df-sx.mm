
axiom df-sx
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vs: setvar s
  assert |- sX = ( s e. _V , t e. _V |-> ( sigaGen ` ran ( x e. s , y e. t |-> ( x X. y ) ) ) )
end
