include "com3r.mm"
include "com23.mm"

theorem com13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume com3.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ch -> ( ps -> ( ph -> th ) ) )

  proof
    wch
    wph
    wps
    wth
    wph
    wps
    wch
    wth
    com3.1
    com3r
    com23
end
