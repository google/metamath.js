include "wa.mm"
include "simpl.mm"
include "pm4.71i.mm"
include "bicomi.mm"

theorem anabs1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) )

  proof
    wph
    wps
    wa
    #
    @0
    wph
    wa
    @0
    wph
    wph
    wps
    simpl
    pm4.71i
    bicomi
end
