
axiom df-diag
  let vc: setvar c
  let vd: setvar d
  assert |- DiagFunc = ( c e. Cat , d e. Cat |-> ( <. c , d >. curryF ( c 1stF d ) ) )
end
