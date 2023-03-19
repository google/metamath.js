include "wo.mm"
include "oridm.mm"
include "bicomi.mm"

theorem pm4.25
  let wph: wff ph


  assert |- ( ph <-> ( ph \/ ph ) )

  proof
    wph
    wph
    wo
    wph
    wph
    oridm
    bicomi
end
