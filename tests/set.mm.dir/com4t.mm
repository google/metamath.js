include "com4l.mm"

theorem com4t
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume com4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) )

  proof
    wps
    wch
    wth
    wph
    wta
    wph
    wps
    wch
    wth
    wta
    com4.1
    com4l
    com4l
end
