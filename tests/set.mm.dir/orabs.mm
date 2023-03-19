include "wo.mm"
include "orc.mm"
include "pm4.71ri.mm"

theorem orabs
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph <-> ( ( ph \/ ps ) /\ ph ) )

  proof
    wph
    wph
    wps
    wo
    wph
    wps
    orc
    pm4.71ri
end
