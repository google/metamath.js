

axiom df-or
  param wph: wff ph
  param wps: wff ps
  assert |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) )
end
