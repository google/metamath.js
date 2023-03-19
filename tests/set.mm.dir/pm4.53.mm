include "wn.mm"
include "wo.mm"
include "wa.mm"
include "pm4.52.mm"
include "con2bii.mm"
include "bicomi.mm"

theorem pm4.53
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) )

  proof
    wph
    wn
    wps
    wo
    #
    wph
    wps
    wn
    wa
    #
    wn
    @1
    @0
    wph
    wps
    pm4.52
    con2bii
    bicomi
end
