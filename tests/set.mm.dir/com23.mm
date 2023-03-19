include "wi.mm"
include "pm2.27.mm"
include "syl9.mm"

theorem com23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
