include "wi.mm"
include "com24.mm"
include "com45.mm"

theorem com25
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) )

  proof
    wph
    wth
    wch
    wta
    wps
    wet
    wi
    wph
    wth
    wch
    wps
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    com5.1
    com24
    com45
    com24
end
