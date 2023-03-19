include "wi.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "ralrimiva.mm"
include "ss2rab.mm"
include "sylibr.mm"

theorem ss2rabdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ss2rabdv.1: |- ( ( ph /\ x e. A ) -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> { x e. A | ps } C_ { x e. A | ch } )

  proof
    wph
    wps
    wch
    wi
    #
    vx
    cA
    wral
    wps
    vx
    cA
    crab
    wch
    vx
    cA
    crab
    wss
    wph
    @0
    vx
    cA
    ss2rabdv.1
    ralrimiva
    wps
    wch
    vx
    cA
    ss2rab
    sylibr
end
