
axiom df-opab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- { <. x , y >. | ph } = { z | E. x E. y ( z = <. x , y >. /\ ph ) }
end
