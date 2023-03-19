include "wn.mm"
include "wa.mm"
include "wo.mm"
include "pm3.24.mm"
include "biorfi.mm"
include "ordi.mm"
include "bitri.mm"

theorem pm4.43
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) )

  proof
    wph
    wph
    wps
    wps
    wn
    #
    wa
    #
    wo
    wph
    wps
    wo
    wph
    @0
    wo
    wa
    @1
    wph
    wps
    pm3.24
    biorfi
    wph
    wps
    @0
    ordi
    bitri
end
