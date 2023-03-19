include "wi.mm"
include "com3l.mm"
include "com34.mm"

theorem com4l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume com4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) )

  proof
    wps
    wch
    wph
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    com4.1
    com3l
    com34
end
