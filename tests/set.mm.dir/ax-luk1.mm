
axiom ax-luk1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )
end
