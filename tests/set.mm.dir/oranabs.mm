include "wn.mm"
include "wo.mm"
include "biortn.mm"
include "orcom.mm"
include "syl6rbb.mm"
include "pm5.32ri.mm"

theorem oranabs
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) )

  proof
    wps
    wph
    wps
    wn
    #
    wo
    #
    wph
    wps
    wph
    @0
    wph
    wo
    @1
    wps
    wph
    biortn
    @0
    wph
    orcom
    syl6rbb
    pm5.32ri
end
