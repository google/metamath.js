include "wn.mm"
include "con2i.mm"
include "con3i.mm"
include "pm2.61i.mm"

theorem pm2.65i
  param wph: wff ph
  param wps: wff ps
  assume pm2.65i.1: |- ( ph -> ps )
  assume pm2.65i.2: |- ( ph -> -. ps )


  assert |- -. ph

  proof
    wps
    wph
    wn
    wph
    wps
    pm2.65i.2
    con2i
    wph
    wps
    pm2.65i.1
    con3i
    pm2.61i
end
