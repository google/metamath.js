include "wn.mm"
include "wi.mm"
include "pm2.18.mm"
include "syl.mm"

theorem pm2.18d
  let wph: wff ph
  let wps: wff ps
  assume pm2.18d.1: |- ( ph -> ( -. ps -> ps ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wn
    wps
    wi
    wps
    pm2.18d.1
    wps
    pm2.18
    syl
end
