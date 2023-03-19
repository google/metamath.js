include "com3r.mm"

theorem com3l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume com3.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ps -> ( ch -> ( ph -> th ) ) )

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
    com3r
end
