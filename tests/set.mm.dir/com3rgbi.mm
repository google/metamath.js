include "wi.mm"
include "pm2.04.mm"
include "com24.mm"
include "com34.mm"
include "impbii.mm"

theorem com3rgbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ( ch -> th ) ) ) <-> ( ch -> ( ph -> ( ps -> th ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    #
    wi
    wi
    #
    wch
    wph
    wps
    wth
    wi
    #
    wi
    wi
    #
    @1
    wps
    wph
    wch
    wth
    wph
    wps
    @0
    pm2.04
    com24
    @3
    wph
    wch
    wps
    wth
    wch
    wph
    @2
    pm2.04
    com34
    impbii
end
