
axiom df-asp
  let vw: setvar w
  let vt: setvar t
  let vs: setvar s
  assert |- AlgSpan = ( w e. AssAlg |-> ( s e. ~P ( Base ` w ) |-> |^| { t e. ( ( SubRing ` w ) i^i ( LSubSp ` w ) ) | s C_ t } ) )
end
