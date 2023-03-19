include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ioran.mm"
include "bicomi.mm"

theorem pm4.56
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) )

  proof
    wph
    wps
    wo
    wn
    wph
    wn
    wps
    wn
    wa
    wph
    wps
    ioran
    bicomi
end
