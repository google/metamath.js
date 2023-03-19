include "wn.mm"
include "a1i.mm"
include "pm2.65i.mm"

theorem mto
  let wph: wff ph
  let wps: wff ps
  assume mto.1: |- -. ps
  assume mto.2: |- ( ph -> ps )


  assert |- -. ph

  proof
    wph
    wps
    mto.2
    wps
    wn
    wph
    mto.1
    a1i
    pm2.65i
end
