include "wi.mm"
include "wn.mm"
include "pm2.5.mm"
include "orri.mm"

theorem pm5.11
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) \/ ( -. ph -> ps ) )

  proof
    wph
    wps
    wi
    wph
    wn
    wps
    wi
    wph
    wps
    pm2.5
    orri
end
