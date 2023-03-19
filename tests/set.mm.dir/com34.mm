include "wi.mm"
include "pm2.04.mm"
include "syl6.mm"

theorem com34
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume com4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wi
    wi
    wth
    wch
    wta
    wi
    wi
    com4.1
    wch
    wth
    wta
    pm2.04
    syl6
end
