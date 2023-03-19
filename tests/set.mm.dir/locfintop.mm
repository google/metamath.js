include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
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
include "eqid.mm"
include "islocfin.mm"
include "simp1bi.mm"

theorem locfintop
  let cA: class A
  let cJ: class J
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let cX: class X
  let cY: class Y


  assert |- ( A e. ( LocFin ` J ) -> J e. Top )

  proof
    cA
    cJ
    clocfin
    cfv
    wcel
    cJ
    ctop
    wcel
    cJ
    cuni
    #
    cA
    cuni
    #
    wceq
    vs
    cv
    vn
    cv
    #
    wcel
    vx
    cv
    @2
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
    @0
    wral
    vs
    cA
    vn
    cJ
    @0
    @1
    vx
    @0
    eqid
    @1
    eqid
    islocfin
    simp1bi
end
