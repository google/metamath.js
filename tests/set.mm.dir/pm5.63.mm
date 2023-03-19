include "wn.mm"
include "wa.mm"
include "wo.mm"
include "exmid.mm"
include "ordi.mm"
include "mpbiran.mm"
include "bicomi.mm"

theorem pm5.63
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) )

  proof
    wph
    wph
    wn
    #
    wps
    wa
    wo
    #
    wph
    wps
    wo
    #
    @1
    wph
    @0
    wo
    @2
    wph
    exmid
    wph
    @0
    wps
    ordi
    mpbiran
    bicomi
end
