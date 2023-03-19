include "wa.mm"
include "simpr.mm"
include "eximi.mm"

theorem exsimpr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph /\ ps ) -> E. x ps )

  proof
    wph
    wps
    wa
    wps
    vx
    wph
    wps
    simpr
    eximi
end
