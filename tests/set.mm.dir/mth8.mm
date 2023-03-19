include "wi.mm"
include "pm2.27.mm"
include "con3d.mm"

theorem mth8
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) )

  proof
    wph
    wph
    wps
    wi
    wps
    wph
    wps
    pm2.27
    con3d
end
