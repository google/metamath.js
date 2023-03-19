include "wo.mm"
include "orc.mm"
include "pm4.71i.mm"

theorem pm4.45
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph <-> ( ph /\ ( ph \/ ps ) ) )

  proof
    wph
    wph
    wps
    wo
    wph
    wps
    orc
    pm4.71i
end
