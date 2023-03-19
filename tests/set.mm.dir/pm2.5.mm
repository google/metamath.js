include "wi.mm"
include "wn.mm"
include "simplim.mm"
include "pm2.24d.mm"

theorem pm2.5
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) )

  proof
    wph
    wps
    wi
    wn
    wph
    wps
    wph
    wps
    simplim
    pm2.24d
end
