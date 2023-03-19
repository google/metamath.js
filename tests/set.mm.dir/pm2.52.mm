include "wi.mm"
include "wn.mm"
include "pm2.521.mm"
include "con3d.mm"

theorem pm2.52
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) )

  proof
    wph
    wps
    wi
    wn
    wps
    wph
    wph
    wps
    pm2.521
    con3d
end
