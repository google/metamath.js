include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "orc.mm"
include "xrleloe.mm"
include "syl5ibr.mm"

theorem xrltle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B -> A <_ B ) )

  proof
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cle
    wbr
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    @0
    cA
    cB
    wceq
    #
    wo
    @0
    @1
    orc
    cA
    cB
    xrleloe
    syl5ibr
end
