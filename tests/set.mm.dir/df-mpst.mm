
axiom df-mpst
  let vt: setvar t
  let vd: setvar d
  assert |- mPreSt = ( t e. _V |-> ( ( { d e. ~P ( mDV ` t ) | `' d = d } X. ( ~P ( mEx ` t ) i^i Fin ) ) X. ( mEx ` t ) ) )
end
