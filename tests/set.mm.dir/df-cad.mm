
axiom df-cad
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( cadd ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) )
end
