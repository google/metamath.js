include "wn.mm"
include "wi.mm"
include "pm2.6.mm"
include "com12.mm"

theorem pm2.61
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) )

  proof
    wph
    wn
    wps
    wi
    wph
    wps
    wi
    wps
    wph
    wps
    pm2.6
    com12
end
