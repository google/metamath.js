
theorem iin3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume iin3.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ps -> ( ch -> th ) ) )

  proof
    iin3.1
end
