include "wa.mm"
include "wo.mm"
include "simpl.mm"
include "orim12i.mm"
include "pm4.71ri.mm"

theorem prlem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <-> ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wth
    wa
    #
    wo
    wph
    wch
    wo
    @0
    wph
    @1
    wch
    wph
    wps
    simpl
    wch
    wth
    simpl
    orim12i
    pm4.71ri
end
