
axiom df-ptfin
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- PtFin = { x | A. y e. U. x { z e. x | y e. z } e. Fin }
end
