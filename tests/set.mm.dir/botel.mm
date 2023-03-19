include "wfal.mm"
include "falim.mm"
include "syl.mm"

theorem botel
  let wph: wff ph
  let wps: wff ps
  assume botel.1: |- ( ph -> F. )


  assert |- ( ph -> ps )

  proof
    wph
    wfal
    wps
    botel.1
    wps
    falim
    syl
end
