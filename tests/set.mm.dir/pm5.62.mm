include "wa.mm"
include "wn.mm"
include "wo.mm"
include "exmid.mm"
include "ordir.mm"
include "mpbiran2.mm"

theorem pm5.62
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) )

  proof
    wph
    wps
    wa
    wps
    wn
    #
    wo
    wph
    @0
    wo
    wps
    @0
    wo
    wps
    exmid
    wph
    wps
    @0
    ordir
    mpbiran2
end
