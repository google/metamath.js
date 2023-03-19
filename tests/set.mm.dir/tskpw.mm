include "ctsk.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "eltsk2g.mm"
include "ibi.mm"
include "simpld.mm"
include "simpr.mm"
include "ralimi.mm"
include "syl.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem tskpw
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( T e. Tarski /\ A e. T ) -> ~P A e. T )

  proof
    cT
    ctsk
    wcel
    #
    vx
    cv
    #
    cpw
    #
    cT
    wcel
    #
    vx
    cT
    wral
    #
    cA
    cT
    wcel
    cA
    cpw
    #
    cT
    wcel
    #
    @0
    @2
    cT
    wss
    #
    @3
    wa
    #
    vx
    cT
    wral
    #
    @4
    @0
    @9
    @1
    cT
    cen
    wbr
    @1
    cT
    wcel
    wo
    vx
    cT
    cpw
    wral
    #
    @0
    @9
    @10
    wa
    vx
    cT
    ctsk
    eltsk2g
    ibi
    simpld
    @8
    @3
    vx
    cT
    @7
    @3
    simpr
    ralimi
    syl
    @3
    @6
    vx
    cA
    cT
    @1
    cA
    wceq
    @2
    @5
    cT
    @1
    cA
    pweq
    eleq1d
    rspccva
    sylan
end
