include "wn.mm"
include "wo.mm"
include "wa.mm"
include "pm4.54.mm"
include "con2bii.mm"
include "bicomi.mm"

theorem pm4.55
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) )

  proof
    wph
    wps
    wn
    wo
    #
    wph
    wn
    wps
    wa
    #
    wn
    @1
    @0
    wph
    wps
    pm4.54
    con2bii
    bicomi
end
