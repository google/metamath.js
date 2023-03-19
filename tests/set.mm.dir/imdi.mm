include "wi.mm"
include "ax-2.mm"
include "pm2.86.mm"
include "impbii.mm"

theorem imdi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) <-> ( ( ph -> ps ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wph
    wps
    wi
    wph
    wch
    wi
    wi
    wph
    wps
    wch
    ax-2
    wph
    wps
    wch
    pm2.86
    impbii
end
