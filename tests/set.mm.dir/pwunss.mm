include "cpw.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "wo.mm"
include "wcel.mm"
include "ssun.mm"
include "elun.mm"
include "selpw.mm"
include "orbi12i.mm"
include "bitri.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem pwunss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ~P A u. ~P B ) C_ ~P ( A u. B )

  proof
    vx
    cA
    cpw
    #
    cB
    cpw
    #
    cun
    #
    cA
    cB
    cun
    #
    cpw
    #
    vx
    cv
    #
    cA
    wss
    #
    @5
    cB
    wss
    #
    wo
    #
    @5
    @3
    wss
    @5
    @2
    wcel
    #
    @5
    @4
    wcel
    @5
    cA
    cB
    ssun
    @9
    @5
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wo
    @8
    @5
    @0
    @1
    elun
    @10
    @6
    @11
    @7
    vx
    cA
    selpw
    vx
    cB
    selpw
    orbi12i
    bitri
    vx
    @3
    selpw
    3imtr4i
    ssriv
end
