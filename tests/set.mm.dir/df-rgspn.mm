
axiom df-rgspn
  let vw: setvar w
  let vt: setvar t
  let vs: setvar s
  assert |- RingSpan = ( w e. _V |-> ( s e. ~P ( Base ` w ) |-> |^| { t e. ( SubRing ` w ) | s C_ t } ) )
end
