include "wi.mm"
include "com23.mm"
include "com12.mm"

theorem com3r
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
