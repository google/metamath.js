include "csn.mm"
include "cpw.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "wcel.mm"
include "eqimss.mm"
include "velsn.mm"
include "selpw.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem snsspw
  let cA: class A
  let vx: setvar x


  assert |- { A } C_ ~P A

  proof
    vx
    cA
    csn
    #
    cA
    cpw
    #
    vx
    cv
    #
    cA
    wceq
    @2
    cA
    wss
    @2
    @0
    wcel
    @2
    @1
    wcel
    @2
    cA
    eqimss
    vx
    cA
    velsn
    vx
    cA
    selpw
    3imtr4i
    ssriv
end
