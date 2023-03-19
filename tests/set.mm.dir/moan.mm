include "wa.mm"
include "simpr.mm"
include "moimi.mm"

theorem moan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E* x ph -> E* x ( ps /\ ph ) )

  proof
    wps
    wph
    wa
    wph
    vx
    wps
    wph
    simpr
    moimi
end
