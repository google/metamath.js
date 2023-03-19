include "wi.mm"
include "wo.mm"
include "pm2.621.mm"
include "com12.mm"

theorem pm2.62
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wo
    wps
    wph
    wps
    pm2.621
    com12
end
