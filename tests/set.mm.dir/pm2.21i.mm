include "wn.mm"
include "a1i.mm"
include "con4i.mm"

theorem pm2.21i
  param wph: wff ph
  param wps: wff ps
  assume pm2.21i.1: |- -. ph


  assert |- ( ph -> ps )

  proof
    wps
    wph
    wph
    wn
    wps
    wn
    pm2.21i.1
    a1i
    con4i
end
