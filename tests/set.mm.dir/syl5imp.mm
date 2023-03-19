include "wi.mm"
include "pm2.04.mm"
include "imim2d.mm"
include "com34.mm"

theorem syl5imp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( th -> ps ) -> ( ph -> ( th -> ch ) ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    #
    wth
    wps
    wi
    wth
    wph
    wch
    @0
    wps
    wph
    wch
    wi
    wth
    wph
    wps
    wch
    pm2.04
    imim2d
    com34
end
