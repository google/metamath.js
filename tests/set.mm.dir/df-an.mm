
axiom df-an
  let wph: wff ph
  let wps: wff ps
  assert |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )
end
