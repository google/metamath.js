include "wi.mm"
include "pm2.27.mm"
include "syl9.mm"

theorem com23
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume com3.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ch -> ( ps -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wch
    wth
    com3.1
    wch
    wth
    pm2.27
    syl9
end
