
axiom df-mvrs
  let vt: setvar t
  let ve: setvar e
  assert |- mVars = ( t e. _V |-> ( e e. ( mEx ` t ) |-> ( ran ( 2nd ` e ) i^i ( mVR ` t ) ) ) )
end
