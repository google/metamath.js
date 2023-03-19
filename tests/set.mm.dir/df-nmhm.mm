
axiom df-nmhm
  let vt: setvar t
  let vs: setvar s
  assert |- NMHom = ( s e. NrmMod , t e. NrmMod |-> ( ( s LMHom t ) i^i ( s NGHom t ) ) )
end
