include "wss.mm"
include "wa.mm"
include "ccom.mm"
include "wceq.mm"
include "coss2.mm"
include "anim12i.mm"
include "eqss.mm"
include "3imtr4i.mm"

theorem coeq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C o. A ) = ( C o. B ) )

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
    cC
    cA
    ccom
    #
    cC
    cB
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
    coss2
    cB
    cA
    cC
    coss2
    anim12i
    cA
    cB
    eqss
    @2
    @3
    eqss
    3imtr4i
end
