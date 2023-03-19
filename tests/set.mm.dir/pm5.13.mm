include "pm5.14.mm"

theorem pm5.13
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) \/ ( ps -> ph ) )

  proof
    wph
    wps
    wph
    pm5.14
end
