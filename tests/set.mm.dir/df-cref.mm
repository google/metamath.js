
axiom df-cref
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vj: setvar j
  assert |- CovHasRef A = { j e. Top | A. y e. ~P j ( U. j = U. y -> E. z e. ( ~P j i^i A ) z Ref y ) }
end
