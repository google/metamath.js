
axiom ax-frege52a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assert |- ( ( ph <-> ps ) -> ( if- ( ph , th , ch ) -> if- ( ps , th , ch ) ) )
end
