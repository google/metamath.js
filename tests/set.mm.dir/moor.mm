include "wo.mm"
include "orc.mm"
include "moimi.mm"

theorem moor
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E* x ( ph \/ ps ) -> E* x ph )

  proof
    wph
    wph
    wps
    wo
    vx
    wph
    wps
    orc
    moimi
end
