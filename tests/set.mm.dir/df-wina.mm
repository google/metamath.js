
axiom df-wina
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- InaccW = { x | ( x =/= (/) /\ ( cf ` x ) = x /\ A. y e. x E. z e. x y ~< z ) }
end
