

axiom df-an
  param wph: wff ph
  param wps: wff ps
  assert |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )
end
