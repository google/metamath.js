include "wo.mm"
include "wi.mm"
include "orel1.mm"
include "orri.mm"

theorem pm2.25
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph \/ ( ( ph \/ ps ) -> ps ) )

  proof
    wph
    wph
    wps
    wo
    wps
    wi
    wph
    wps
    orel1
    orri
end
