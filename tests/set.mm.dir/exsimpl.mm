include "wa.mm"
include "simpl.mm"
include "eximi.mm"

theorem exsimpl
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( E. x ( ph /\ ps ) -> E. x ph )

  proof
    wph
    wps
    wa
    wph
    vx
    wph
    wps
    simpl
    eximi
end
