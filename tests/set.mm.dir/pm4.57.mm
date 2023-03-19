include "wo.mm"
include "wn.mm"
include "wa.mm"
include "oran.mm"
include "bicomi.mm"

theorem pm4.57
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) )

  proof
    wph
    wps
    wo
    wph
    wn
    wps
    wn
    wa
    wn
    wph
    wps
    oran
    bicomi
end
