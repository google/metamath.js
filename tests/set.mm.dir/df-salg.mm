
axiom df-salg
  let vx: setvar x
  let vy: setvar y
  assert |- SAlg = { x | ( (/) e. x /\ A. y e. x ( U. x \ y ) e. x /\ A. y e. ~P x ( y ~<_ _om -> U. y e. x ) ) }
end
