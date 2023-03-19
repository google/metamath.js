
axiom df-gim
  let vt: setvar t
  let vg: setvar g
  let vs: setvar s
  assert |- GrpIso = ( s e. Grp , t e. Grp |-> { g e. ( s GrpHom t ) | g : ( Base ` s ) -1-1-onto-> ( Base ` t ) } )
end
