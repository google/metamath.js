include "wi.mm"
include "com23.mm"
include "com12.mm"

theorem com3r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume com3.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ch -> ( ph -> ( ps -> th ) ) )

  proof
    wph
    wch
    wps
    wth
    wi
    wph
    wps
    wch
    wth
    com3.1
    com23
    com12
end
