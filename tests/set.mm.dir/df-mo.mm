
axiom df-mo
  let wph: wff ph
  let vx: setvar x
  assert |- ( E* x ph <-> ( E. x ph -> E! x ph ) )
end
