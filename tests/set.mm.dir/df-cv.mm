
axiom df-cv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- <oH = { <. x , y >. | ( ( x e. CH /\ y e. CH ) /\ ( x C. y /\ -. E. z e. CH ( x C. z /\ z C. y ) ) ) }
end
