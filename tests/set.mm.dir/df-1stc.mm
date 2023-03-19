
axiom df-1stc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  assert |- 1stc = { j e. Top | A. x e. U. j E. y e. ~P j ( y ~<_ _om /\ A. z e. j ( x e. z -> x e. U. ( y i^i ~P z ) ) ) }
end
