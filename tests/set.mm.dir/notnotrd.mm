include "wn.mm"
include "notnotr.mm"
include "syl.mm"

theorem notnotrd
  let wph: wff ph
  let wps: wff ps
  assume notnotrd.1: |- ( ph -> -. -. ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wn
    wn
    wps
    notnotrd.1
    wps
    notnotr
    syl
end
