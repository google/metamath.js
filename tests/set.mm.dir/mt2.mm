include "a1i.mm"
include "pm2.65i.mm"

theorem mt2
  let wph: wff ph
  let wps: wff ps
  assume mt2.1: |- ps
  assume mt2.2: |- ( ph -> -. ps )


  assert |- -. ph

  proof
    wph
    wps
    wps
    wph
    mt2.1
    a1i
    mt2.2
    pm2.65i
end
