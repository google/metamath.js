include "wn.mm"
include "notnot.mm"
include "syl.mm"

theorem notnotd
  let wph: wff ph
  let wps: wff ps
  assume notnotd.1: |- ( ph -> ps )


  assert |- ( ph -> -. -. ps )

  proof
    wph
    wps
    wps
    wn
    wn
    notnotd.1
    wps
    notnot
    syl
end
