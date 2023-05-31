include "wi.mm"
include "pm2.21.mm"
include "con1i.mm"

theorem simplim
  param wph: wff ph
  param wps: wff ps


  assert |- ( -. ( ph -> ps ) -> ph )

  proof
    wph
    wph
    wps
    wi
    wph
    wps
    pm2.21
    con1i
end
