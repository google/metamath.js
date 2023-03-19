
axiom df-top
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- Top = { x | ( A. y e. ~P x U. y e. x /\ A. y e. x A. z e. x ( y i^i z ) e. x ) }
end
