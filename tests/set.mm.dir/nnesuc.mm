include "com.mm"
include "wcel.mm"
include "con0.mm"
include "csuc.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "nnon.mm"
include "onesuc.mm"
include "sylan.mm"

theorem nnesuc
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A ^o suc B ) = ( ( A ^o B ) .o A ) )

  proof
    cA
    com
    wcel
    cA
    con0
    wcel
    cB
    com
    wcel
    cA
    cB
    csuc
    coe
    co
    cA
    cB
    coe
    co
    cA
    comu
    co
    wceq
    cA
    nnon
    cA
    cB
    onesuc
    sylan
end
