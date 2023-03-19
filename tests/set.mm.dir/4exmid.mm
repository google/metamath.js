include "wa.mm"
include "wn.mm"
include "wo.mm"
include "pm5.24.mm"
include "biimpi.mm"
include "orri.mm"

theorem 4exmid
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) )

  proof
    wph
    wps
    wa
    wph
    wn
    #
    wps
    wn
    #
    wa
    wo
    #
    wph
    @1
    wa
    wps
    @0
    wa
    wo
    #
    @2
    wn
    @3
    wph
    wps
    pm5.24
    biimpi
    orri
end
