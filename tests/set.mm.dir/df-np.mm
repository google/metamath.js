
axiom df-np
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- P. = { x | ( ( (/) C. x /\ x C. Q. ) /\ A. y e. x ( A. z ( z <Q y -> z e. x ) /\ E. z e. x y <Q z ) ) }
end
