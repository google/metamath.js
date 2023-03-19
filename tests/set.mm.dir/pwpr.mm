include "cpr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "wcel.mm"
include "wo.mm"
include "wceq.mm"
include "sspr.mm"
include "vex.mm"
include "elpr.mm"
include "orbi12i.mm"
include "bitr4i.mm"
include "selpw.mm"
include "elun.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem pwpr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C
  let vy: setvar y


  assert |- ~P { A , B } = ( { (/) , { A } } u. { { B } , { A , B } } )

  proof
    vx
    cA
    cB
    cpr
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
    @0
    cpr
    #
    cun
    #
    vx
    cv
    #
    @0
    wss
    #
    @7
    @3
    wcel
    #
    @7
    @5
    wcel
    #
    wo
    #
    @7
    @1
    wcel
    @7
    @6
    wcel
    @8
    @7
    c0
    wceq
    @7
    @2
    wceq
    wo
    #
    @7
    @4
    wceq
    @7
    @0
    wceq
    wo
    #
    wo
    @11
    @7
    cA
    cB
    sspr
    @9
    @12
    @10
    @13
    @7
    c0
    @2
    vx
    vex
    #
    elpr
    @7
    @4
    @0
    @14
    elpr
    orbi12i
    bitr4i
    vx
    @0
    selpw
    @7
    @3
    @5
    elun
    3bitr4i
    eqriv
end
