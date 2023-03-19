include "wi.mm"
include "com5l.mm"
include "com4r.mm"

theorem com15
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) )

  proof
    wps
    wch
    wth
    wta
    wph
    wet
    wi
    wph
    wps
    wch
    wth
    wta
    wet
    com5.1
    com5l
    com4r
end
