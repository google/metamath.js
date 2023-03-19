include "wo.mm"
include "wfal.mm"
include "orim1i.mm"
include "falim.mm"
include "id.mm"
include "jaoi.mm"
include "syl.mm"

theorem orfa2
  let wph: wff ph
  let wps: wff ps
  assume orfa2.1: |- ( ph -> F. )


  assert |- ( ( ph \/ ps ) -> ps )

  proof
    wph
    wps
    wo
    wfal
    wps
    wo
    wps
    wph
    wfal
    wps
    orfa2.1
    orim1i
    wfal
    wps
    wps
    wps
    falim
    wps
    id
    jaoi
    syl
end
