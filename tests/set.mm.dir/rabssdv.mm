include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "rabss.mm"
include "sylibr.mm"

theorem rabssdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabssdv.1: |- ( ( ph /\ x e. A /\ ps ) -> x e. B )

  disjoint B x
  disjoint ph x
  assert |- ( ph -> { x e. A | ps } C_ B )

  proof
    wph
    wps
    vx
    cv
    #
    cB
    wcel
    #
    wi
    #
    vx
    cA
    wral
    wps
    vx
    cA
    crab
    cB
    wss
    wph
    @2
    vx
    cA
    wph
    @0
    cA
    wcel
    wps
    @1
    rabssdv.1
    3exp
    ralrimiv
    wps
    vx
    cA
    cB
    rabss
    sylibr
end
