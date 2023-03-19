include "wi.mm"
include "wo.mm"
include "pm2.21.mm"
include "orri.mm"
include "a1i.mm"

theorem tsim2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ph \/ ( ph -> ps ) ) )

  proof
    wph
    wph
    wps
    wi
    #
    wo
    wth
    wph
    @0
    wph
    wps
    pm2.21
    orri
    a1i
end
