include "wi.mm"
include "ax-1.mm"
include "syl5.mm"
include "com23.mm"

theorem pm2.86d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume pm2.86d.1: |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) )


  assert |- ( ph -> ( ps -> ( ch -> th ) ) )

  proof
    wph
    wch
    wps
    wth
    wch
    wps
    wch
    wi
    wph
    wps
    wth
    wi
    wch
    wps
    ax-1
    pm2.86d.1
    syl5
    com23
end
