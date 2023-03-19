include "crab.mm"
include "nfv.mm"
include "nfrab1.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "simprr.mm"
include "jca.mm"
include "ex.mm"
include "rabid.mm"
include "3imtr4g.mm"
include "ssrd.mm"

theorem rabss3d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabss3d.1: |- ( ( ph /\ ( x e. A /\ ps ) ) -> x e. B )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> { x e. A | ps } C_ { x e. B | ps } )

  proof
    wph
    vx
    wps
    vx
    cA
    crab
    #
    wps
    vx
    cB
    crab
    #
    wph
    vx
    nfv
    wps
    vx
    cA
    nfrab1
    wps
    vx
    cB
    nfrab1
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    @2
    cB
    wcel
    #
    wps
    wa
    #
    @2
    @0
    wcel
    @2
    @1
    wcel
    wph
    @4
    @6
    wph
    @4
    wa
    @5
    wps
    rabss3d.1
    wph
    @3
    wps
    simprr
    jca
    ex
    wps
    vx
    cA
    rabid
    wps
    vx
    cB
    rabid
    3imtr4g
    ssrd
end
