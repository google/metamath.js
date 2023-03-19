include "wss.mm"
include "wa.mm"
include "cdm.mm"
include "wceq.mm"
include "dmss.mm"
include "anim12i.mm"
include "eqss.mm"
include "3imtr4i.mm"

theorem dmeq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> dom A = dom B )

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
    cdm
    #
    cB
    cdm
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
    dmss
    cB
    cA
    dmss
    anim12i
    cA
    cB
    eqss
    @2
    @3
    eqss
    3imtr4i
end
