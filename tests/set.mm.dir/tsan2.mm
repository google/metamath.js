include "wa.mm"
include "wn.mm"
include "wo.mm"
include "pm3.14.mm"
include "orcs.mm"
include "orri.mm"
include "a1i.mm"

theorem tsan2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ph \/ -. ( ph /\ ps ) ) )

  proof
    wph
    wph
    wps
    wa
    wn
    #
    wo
    wth
    wph
    @0
    wph
    wn
    wps
    wn
    @0
    wph
    wps
    pm3.14
    orcs
    orri
    a1i
end
