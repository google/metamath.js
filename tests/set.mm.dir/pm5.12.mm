include "wi.mm"
include "wn.mm"
include "pm2.51.mm"
include "orri.mm"

theorem pm5.12
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) \/ ( ph -> -. ps ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wn
    wi
    wph
    wps
    pm2.51
    orri
end
