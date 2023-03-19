include "wi.mm"
include "pm2.04.mm"
include "syl8.mm"

theorem com45
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    wta
    wth
    wet
    wi
    wi
    com5.1
    wth
    wta
    wet
    pm2.04
    syl8
end
