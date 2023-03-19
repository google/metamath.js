include "wo.mm"
include "wi.mm"
include "pm2.62.mm"
include "pm2.68.mm"
include "impbii.mm"

theorem dfor2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) )

  proof
    wph
    wps
    wo
    wph
    wps
    wi
    wps
    wi
    wph
    wps
    pm2.62
    wph
    wps
    pm2.68
    impbii
end
