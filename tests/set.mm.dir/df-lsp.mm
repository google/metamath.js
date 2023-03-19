
axiom df-lsp
  let vw: setvar w
  let vt: setvar t
  let vs: setvar s
  assert |- LSpan = ( w e. _V |-> ( s e. ~P ( Base ` w ) |-> |^| { t e. ( LSubSp ` w ) | s C_ t } ) )
end
