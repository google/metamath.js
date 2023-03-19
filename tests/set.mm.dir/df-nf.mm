

axiom df-nf
  param wph: wff ph
  param vx: setvar x
  assert |- ( F/ x ph <-> ( E. x ph -> A. x ph ) )
end
