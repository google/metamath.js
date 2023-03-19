include "wi.mm"
include "com4l.mm"
include "com3r.mm"

theorem com14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume com4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) )

  proof
    wps
    wch
    wth
    wph
    wta
    wi
    wph
    wps
    wch
    wth
    wta
    com4.1
    com4l
    com3r
end
