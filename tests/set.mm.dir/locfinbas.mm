include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "islocfin.mm"
include "simp2bi.mm"

theorem locfinbas
  let cA: class A
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  assume locfinbas.1: |- X = U. J
  assume locfinbas.2: |- Y = U. A


  assert |- ( A e. ( LocFin ` J ) -> X = Y )

  proof
    cA
    cJ
    clocfin
    cfv
    wcel
    cJ
    ctop
    wcel
    cX
    cY
    wceq
    vs
    cv
    vn
    cv
    #
    wcel
    vx
    cv
    @0
    cin
    c0
    wne
    vx
    cA
    crab
    cfn
    wcel
    wa
    vn
    cJ
    wrex
    vs
    cX
    wral
    vs
    cA
    vn
    cJ
    cX
    cY
    vx
    locfinbas.1
    locfinbas.2
    islocfin
    simp2bi
end
