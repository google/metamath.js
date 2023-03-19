include "wb.mm"
include "wral.mm"
include "crab.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "rabbi.mm"
include "sylib.mm"

theorem rabbidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rabbidva.1: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> { x e. A | ps } = { x e. A | ch } )

  proof
    wph
    wps
    wch
    wb
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
    wceq
    wph
    @0
    vx
    cA
    rabbidva.1
    ralrimiva
    wps
    wch
    vx
    cA
    rabbi
    sylib
end
