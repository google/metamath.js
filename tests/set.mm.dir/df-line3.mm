
axiom df-line3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- line3 = { x e. ~P RR3 | ( 2o ~<_ x /\ A. y e. x A. z e. x ( z =/= y -> ran PtDf ( y , z ) = x ) ) }
end
