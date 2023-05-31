include "wi.mm"
include "pm2.04.mm"
include "impbii.mm"

theorem bi2.04
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wps
    wph
    wch
    wi
    wi
    wph
    wps
    wch
    pm2.04
    wps
    wph
    wch
    pm2.04
    impbii
end
