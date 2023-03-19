include "wi.mm"
include "pm2.21.mm"
include "orri.mm"

theorem bj-curry
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph \/ ( ph -> ps ) )

  proof
    wph
    wph
    wps
    wi
    wph
    wps
    pm2.21
    orri
end
