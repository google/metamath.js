

axiom ax-2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )
end
