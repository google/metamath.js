
axiom ax-frege8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )
end
