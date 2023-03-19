
axiom df-dmd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- MH* = { <. x , y >. | ( ( x e. CH /\ y e. CH ) /\ A. z e. CH ( y C_ z -> ( ( z i^i x ) vH y ) = ( z i^i ( x vH y ) ) ) ) }
end
