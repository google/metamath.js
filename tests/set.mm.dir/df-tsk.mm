
axiom df-tsk
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- Tarski = { y | ( A. z e. y ( ~P z C_ y /\ E. w e. y ~P z C_ w ) /\ A. z e. ~P y ( z ~~ y \/ z e. y ) ) }
end
