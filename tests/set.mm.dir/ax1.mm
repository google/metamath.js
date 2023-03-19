include "luklem5.mm"

theorem ax1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ph ) )

  proof
    wph
    wps
    luklem5
end
