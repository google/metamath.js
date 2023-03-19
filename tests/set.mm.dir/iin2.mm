
theorem iin2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume iin2.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    iin2.1
end
