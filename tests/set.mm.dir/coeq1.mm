include "wss.mm"
include "wa.mm"
include "ccom.mm"
include "wceq.mm"
include "coss1.mm"
include "anim12i.mm"
include "eqss.mm"
include "3imtr4i.mm"

theorem coeq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A o. C ) = ( B o. C ) )

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    cA
    cC
    ccom
    #
    cB
    cC
    ccom
    #
    wss
    #
    @3
    @2
    wss
    #
    wa
    cA
    cB
    wceq
    @2
    @3
    wceq
    @0
    @4
    @1
    @5
    cA
    cB
    cC
    coss1
    cB
    cA
    cC
    coss1
    anim12i
    cA
    cB
    eqss
    @2
    @3
    eqss
    3imtr4i
end
