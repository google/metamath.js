
axiom df-3nand
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assert |- ( ( ph -/\ ps -/\ ch ) <-> ( ph -> ( ps -> -. ch ) ) )
end
