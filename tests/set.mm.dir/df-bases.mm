
axiom df-bases
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- TopBases = { x | A. y e. x A. z e. x ( y i^i z ) C_ U. ( x i^i ~P ( y i^i z ) ) }
end
