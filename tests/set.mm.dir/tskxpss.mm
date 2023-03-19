include "ctsk.mm"
include "wcel.mm"
include "wss.mm"
include "cxp.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "elxp2.mm"
include "wi.mm"
include "w3a.mm"
include "tskop.mm"
include "eleq1a.mm"
include "syl.mm"
include "3expib.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "xpss12.mm"
include "sstr.mm"
include "expcom.mm"
include "syl2im.mm"
include "3impib.mm"

theorem tskxpss
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( T e. Tarski /\ A C_ T /\ B C_ T ) -> ( A X. B ) C_ T )

  proof
    cT
    ctsk
    wcel
    #
    cA
    cT
    wss
    #
    cB
    cT
    wss
    #
    cA
    cB
    cxp
    #
    cT
    wss
    #
    @0
    cT
    cT
    cxp
    #
    cT
    wss
    #
    @1
    @2
    wa
    @3
    @5
    wss
    #
    @4
    @0
    vz
    @5
    cT
    vz
    cv
    #
    @5
    wcel
    @8
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    cT
    wrex
    vx
    cT
    wrex
    @0
    @8
    cT
    wcel
    #
    vx
    vy
    @8
    cT
    cT
    elxp2
    @0
    @12
    @13
    vx
    vy
    cT
    cT
    @0
    @9
    cT
    wcel
    #
    @10
    cT
    wcel
    #
    @12
    @13
    wi
    #
    @0
    @14
    @15
    w3a
    @11
    cT
    wcel
    @16
    @9
    @10
    cT
    tskop
    @11
    cT
    @8
    eleq1a
    syl
    3expib
    rexlimdvv
    syl5bi
    ssrdv
    cA
    cT
    cB
    cT
    xpss12
    @7
    @6
    @4
    @3
    @5
    cT
    sstr
    expcom
    syl2im
    3impib
end
