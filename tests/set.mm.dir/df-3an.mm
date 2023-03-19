

axiom df-3an
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assert |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) )
end
