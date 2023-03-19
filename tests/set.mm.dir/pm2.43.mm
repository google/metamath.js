include "wi.mm"
include "pm2.27.mm"
include "a2i.mm"

theorem pm2.43
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) )

  proof
    wph
    wph
    wps
    wi
    wps
    wph
    wps
    pm2.27
    a2i
end
