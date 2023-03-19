
axiom df-reg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  assert |- Reg = { j e. Top | A. x e. j A. y e. x E. z e. j ( y e. z /\ ( ( cls ` j ) ` z ) C_ x ) }
end
