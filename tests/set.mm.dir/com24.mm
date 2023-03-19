include "wi.mm"
include "com4t.mm"
include "com13.mm"

theorem com24
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume com4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) )

  proof
    wch
    wth
    wph
    wps
    wta
    wi
    wph
    wps
    wch
    wth
    wta
    com4.1
    com4t
    com13
end
