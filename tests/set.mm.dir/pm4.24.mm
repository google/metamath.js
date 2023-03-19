include "id.mm"
include "pm4.71i.mm"

theorem pm4.24
  let wph: wff ph


  assert |- ( ph <-> ( ph /\ ph ) )

  proof
    wph
    wph
    wph
    id
    pm4.71i
end
