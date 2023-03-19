
axiom df-toplnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- TopLnd = { x e. Top | A. y e. ~P x ( U. x = U. y -> E. z e. ~P x ( z ~<_ _om /\ U. x = U. z ) ) }
end
