include "wo.mm"
include "pm1.2.mm"
include "pm2.07.mm"
include "impbii.mm"

theorem oridm
  let wph: wff ph


  assert |- ( ( ph \/ ph ) <-> ph )

  proof
    wph
    wph
    wo
    wph
    wph
    pm1.2
    wph
    pm2.07
    impbii
end
