include "wa.mm"
include "simpl.mm"
include "eximi.mm"

theorem exsimpl
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


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
