include "ctsk.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "eltskg.mm"
include "ibi.mm"
include "simpld.mm"
include "simpl.mm"
include "ralimi.mm"
include "syl.mm"
include "wceq.mm"
include "pweq.mm"
include "sseq1d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem tskpwss
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( T e. Tarski /\ A e. T ) -> ~P A C_ T )

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
    wss
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
    wss
    #
    @0
    @3
    @2
    vy
    cv
    wss
    vy
    cT
    wrex
    #
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
    vy
    cT
    ctsk
    eltskg
    ibi
    simpld
    @8
    @3
    vx
    cT
    @3
    @7
    simpl
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
    sseq1d
    rspccva
    sylan
end
