
theorem iin1
  let wph: wff ph
  let wps: wff ps
  assume iin1.1: |- ( ph -> ps )


  assert |- ( ph -> ps )

  proof
    iin1.1
end
