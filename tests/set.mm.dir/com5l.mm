include "wi.mm"
include "com4l.mm"
include "com45.mm"

theorem com5l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) )

  proof
    wps
    wch
    wth
    wph
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
    com4l
    com45
end
