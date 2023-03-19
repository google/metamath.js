include "ctsk.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "eltskg.mm"
include "ibi.mm"
include "simprd.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "wceq.mm"
include "breq1.mm"
include "eleq1.mm"
include "orbi12d.mm"
include "rspccva.mm"
include "syl2an2r.mm"

theorem tsken
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( T e. Tarski /\ A C_ T ) -> ( A ~~ T \/ A e. T ) )

  proof
    cT
    ctsk
    wcel
    #
    vx
    cv
    #
    cT
    cen
    wbr
    #
    @1
    cT
    wcel
    #
    wo
    #
    vx
    cT
    cpw
    #
    wral
    #
    cA
    cT
    wss
    #
    cA
    @5
    wcel
    #
    cA
    cT
    cen
    wbr
    #
    cA
    cT
    wcel
    #
    wo
    #
    @0
    @1
    cpw
    #
    cT
    wss
    @12
    vy
    cv
    wss
    vy
    cT
    wrex
    wa
    vx
    cT
    wral
    #
    @6
    @0
    @13
    @6
    wa
    vx
    vy
    cT
    ctsk
    eltskg
    ibi
    simprd
    @0
    @8
    @7
    cA
    cT
    ctsk
    elpw2g
    biimpar
    @4
    @11
    vx
    cA
    @5
    @1
    cA
    wceq
    @2
    @9
    @3
    @10
    @1
    cA
    cT
    cen
    breq1
    @1
    cA
    cT
    eleq1
    orbi12d
    rspccva
    syl2an2r
end
