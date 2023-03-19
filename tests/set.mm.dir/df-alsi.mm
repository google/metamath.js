
axiom df-alsi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assert |- ( A! x ( ph -> ps ) <-> ( A. x ( ph -> ps ) /\ E. x ph ) )
end
