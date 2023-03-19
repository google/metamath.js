
axiom df-cmp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- Comp = { x e. Top | A. y e. ~P x ( U. x = U. y -> E. z e. ( ~P y i^i Fin ) U. x = U. z ) }
end
