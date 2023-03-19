
axiom df-cmgm2
  let vm: setvar m
  assert |- CMgmALT = { m e. MgmALT | ( +g ` m ) comLaw ( Base ` m ) }
end
