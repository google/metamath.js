include "wa.mm"
include "pm4.24.mm"
include "bicomi.mm"

theorem anidm
  let wph: wff ph


  assert |- ( ( ph /\ ph ) <-> ph )

  proof
    wph
    wph
    wph
    wa
    wph
    pm4.24
    bicomi
end
