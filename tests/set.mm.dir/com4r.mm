include "com4t.mm"
include "com4l.mm"

theorem com4r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume com4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) )

  proof
    wch
    wth
    wph
    wps
    wta
    wph
    wps
    wch
    wth
    wta
    com4.1
    com4t
    com4l
end
