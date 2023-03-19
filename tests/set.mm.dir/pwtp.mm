include "ctp.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "selpw.mm"
include "wo.mm"
include "wceq.mm"
include "elun.mm"
include "vex.mm"
include "elpr.mm"
include "orbi12i.mm"
include "bitri.mm"
include "sstp.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem pwtp
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ~P { A , B , C } = ( ( { (/) , { A } } u. { { B } , { A , B } } ) u. ( { { C } , { A , C } } u. { { B , C } , { A , B , C } } ) )

  proof
    vx
    cA
    cB
    cC
    ctp
    #
    cpw
    #
    c0
    cA
    csn
    #
    cpr
    #
    cB
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    cun
    #
    cC
    csn
    #
    cA
    cC
    cpr
    #
    cpr
    #
    cB
    cC
    cpr
    #
    @0
    cpr
    #
    cun
    #
    cun
    #
    vx
    cv
    #
    @1
    wcel
    @15
    @0
    wss
    #
    @15
    @14
    wcel
    #
    vx
    @0
    selpw
    @15
    @7
    wcel
    #
    @15
    @13
    wcel
    #
    wo
    @15
    c0
    wceq
    @15
    @2
    wceq
    wo
    #
    @15
    @4
    wceq
    @15
    @5
    wceq
    wo
    #
    wo
    #
    @15
    @8
    wceq
    @15
    @9
    wceq
    wo
    #
    @15
    @11
    wceq
    @15
    @0
    wceq
    wo
    #
    wo
    #
    wo
    @17
    @16
    @18
    @22
    @19
    @25
    @18
    @15
    @3
    wcel
    #
    @15
    @6
    wcel
    #
    wo
    @22
    @15
    @3
    @6
    elun
    @26
    @20
    @27
    @21
    @15
    c0
    @2
    vx
    vex
    #
    elpr
    @15
    @4
    @5
    @28
    elpr
    orbi12i
    bitri
    @19
    @15
    @10
    wcel
    #
    @15
    @12
    wcel
    #
    wo
    @25
    @15
    @10
    @12
    elun
    @29
    @23
    @30
    @24
    @15
    @8
    @9
    @28
    elpr
    @15
    @11
    @0
    @28
    elpr
    orbi12i
    bitri
    orbi12i
    @15
    @7
    @13
    elun
    @15
    cA
    cB
    cC
    sstp
    3bitr4ri
    bitri
    eqriv
end
