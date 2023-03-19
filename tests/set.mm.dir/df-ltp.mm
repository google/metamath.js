
axiom df-ltp
  let vx: setvar x
  let vy: setvar y
  assert |- <P = { <. x , y >. | ( ( x e. P. /\ y e. P. ) /\ x C. y ) }
end
