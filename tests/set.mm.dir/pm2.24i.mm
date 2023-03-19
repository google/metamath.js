include "wn.mm"
include "a1i.mm"
include "con1i.mm"

theorem pm2.24i
  let wph: wff ph
  let wps: wff ps
  assume pm2.24i.1: |- ph


  assert |- ( -. ph -> ps )

  proof
    wps
    wph
    wph
    wps
    wn
    pm2.24i.1
    a1i
    con1i
end
