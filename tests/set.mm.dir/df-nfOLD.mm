
axiom df-nfOLD
  let wph: wff ph
  let vx: setvar x
  assert |- ( nfOLD x ph <-> A. x ( ph -> A. x ph ) )
end
