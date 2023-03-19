include "wi.mm"
include "wo.mm"
include "orimdi.mm"
include "biimpri.mm"

theorem pm2.85
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ps ) -> ( ph \/ ch ) ) -> ( ph \/ ( ps -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wo
    wph
    wps
    wo
    wph
    wch
    wo
    wi
    wph
    wps
    wch
    orimdi
    biimpri
end
