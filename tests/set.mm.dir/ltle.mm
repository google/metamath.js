include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "orc.mm"
include "leloe.mm"
include "syl5ibr.mm"

theorem ltle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B -> A <_ B ) )

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
    cr
    wcel
    cB
    cr
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
    leloe
    syl5ibr
end
