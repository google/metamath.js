include "wi.mm"
include "pm2.27.mm"
include "imori.mm"

theorem pm2.26
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph \/ ( ( ph -> ps ) -> ps ) )

  proof
    wph
    wph
    wps
    wi
    wps
    wi
    wph
    wps
    pm2.27
    imori
end
