
axiom ax-sep
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) )
end
