include "wn.mm"
include "pm2.65i.mm"
include "notnotri.mm"

theorem pm2.65ni
  let wph: wff ph
  let wps: wff ps
  assume pm2.65ni.1: |- ( -. ph -> ps )
  assume pm2.65ni.2: |- ( -. ph -> -. ps )


  assert |- ph

  proof
    wph
    wph
    wn
    wps
    pm2.65ni.1
    pm2.65ni.2
    pm2.65i
    notnotri
end
