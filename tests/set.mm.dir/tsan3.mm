include "wa.mm"
include "wn.mm"
include "wo.mm"
include "pm3.14.mm"
include "olcs.mm"
include "orri.mm"
include "a1i.mm"

theorem tsan3
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ps \/ -. ( ph /\ ps ) ) )

  proof
    wps
    wph
    wps
    wa
    wn
    #
    wo
    wth
    wps
    @0
    wph
    wn
    wps
    wn
    @0
    wph
    wps
    pm3.14
    olcs
    orri
    a1i
end
