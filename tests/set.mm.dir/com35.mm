include "wi.mm"
include "com34.mm"
include "com45.mm"

theorem com35
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) )

  proof
    wph
    wps
    wth
    wta
    wch
    wet
    wi
    wph
    wps
    wth
    wch
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
    com34
    com45
    com34
end
