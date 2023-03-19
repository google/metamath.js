include "csuc.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wtr.mm"
include "wss.mm"
include "elsuci.mm"
include "trss.mm"
include "wi.mm"
include "eqimss.mm"
include "a1i.mm"
include "jaod.mm"
include "syl5.mm"

theorem trsucss
  let cA: class A
  let cB: class B


  assert |- ( Tr A -> ( B e. suc A -> B C_ A ) )

  proof
    cB
    cA
    csuc
    wcel
    cB
    cA
    wcel
    #
    cB
    cA
    wceq
    #
    wo
    cA
    wtr
    #
    cB
    cA
    wss
    #
    cB
    cA
    elsuci
    @2
    @0
    @3
    @1
    cA
    cB
    trss
    @1
    @3
    wi
    @2
    cB
    cA
    eqimss
    a1i
    jaod
    syl5
end
