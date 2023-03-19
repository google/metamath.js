
axiom df-lmim
  let vt: setvar t
  let vg: setvar g
  let vs: setvar s
  assert |- LMIso = ( s e. LMod , t e. LMod |-> { g e. ( s LMHom t ) | g : ( Base ` s ) -1-1-onto-> ( Base ` t ) } )
end
