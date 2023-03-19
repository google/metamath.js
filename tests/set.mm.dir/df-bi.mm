
axiom df-bi
  let wph: wff ph
  let wps: wff ps
  assert |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) )
end
