
axiom df-nrm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  assert |- Nrm = { j e. Top | A. x e. j A. y e. ( ( Clsd ` j ) i^i ~P x ) E. z e. j ( y C_ z /\ ( ( cls ` j ) ` z ) C_ x ) }
end
