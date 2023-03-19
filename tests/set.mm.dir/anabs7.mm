include "wa.mm"
include "simpr.mm"
include "pm4.71ri.mm"
include "bicomi.mm"

theorem anabs7
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) )

  proof
    wph
    wps
    wa
    #
    wps
    @0
    wa
    @0
    wps
    wph
    wps
    simpr
    pm4.71ri
    bicomi
end
