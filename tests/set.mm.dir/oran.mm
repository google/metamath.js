include "wn.mm"
include "wa.mm"
include "wo.mm"
include "pm4.56.mm"
include "con2bii.mm"

theorem oran
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) )

  proof
    wph
    wn
    wps
    wn
    wa
    wph
    wps
    wo
    wph
    wps
    pm4.56
    con2bii
end
