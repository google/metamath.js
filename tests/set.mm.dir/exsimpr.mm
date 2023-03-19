include "wa.mm"
include "simpr.mm"
include "eximi.mm"

theorem exsimpr
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


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
